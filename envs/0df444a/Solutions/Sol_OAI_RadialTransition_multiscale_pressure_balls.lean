-- Prove2me | solution 1 for OAI.RadialTransition.multiscale_pressure_balls
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:14:56.073192+00:00
-- url     : https://prove2.me/submissions/a2668bdb-ac1d-42e3-a242-88a6ed7f67c7

import Mathlib
import Definitions.Def_RadialDensityInterval
import Definitions.Def_OAIQWRTD000

section
-- module Solutions.OAIQW_RadialTransition.IdealAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem active_parabola {Q : Pressure} {a β h u : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hu : ActiveShift Q a β h u) (r : ℝ) :
    Q β (h + β * a * u + r) ≤
      Q β (h + β * a * u) + u * r + r ^ 2 / (2 * β * a) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hshift : h + β * a * (u + r / (β * a)) = h + β * a * u + r := by
    field_simp
    ring
  have hc := hu (u + r / (β * a))
  dsimp [attractionBranch] at hc
  rw [hshift] at hc
  calc
    Q β (h + β * a * u + r) ≤ Q β (h + β * a * u) +
        β * a / 2 * ((u + r / (β * a)) ^ 2 - u ^ 2) := by linarith
    _ = Q β (h + β * a * u) + u * r + r ^ 2 / (2 * β * a) := by
      field_simp
      ring

theorem active_support_density {Q : Pressure} {a β h u e d : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hu : ActiveShift Q a β h u)
    (hs : pressureSupport Q β (h + β * a * u) e d) : d = u := by
  have hba : 0 < β * a := mul_pos hβ ha
  have hqa : ∀ r : ℝ, d * r ≤ u * r + r ^ 2 / (2 * β * a) := by
    intro r
    have hl := hs β (h + β * a * u + r) hβ
    have hr := active_parabola ha hβ hu r
    simp only [sub_self, mul_zero, add_zero, add_sub_cancel_left] at hl
    linarith
  have hh := hqa ((β * a) * (d - u))
  have hden : 0 < 2 * β * a := by positivity
  have hh' : (d * ((β * a) * (d - u)) - u * ((β * a) * (d - u))) *
      (2 * β * a) ≤ ((β * a) * (d - u)) ^ 2 :=
    (le_div_iff₀ hden).mp (by linarith [hh])
  have hz : (β * a) ^ 2 * (d - u) ^ 2 ≤ 0 := by nlinarith [hh']
  have hd : (d - u) ^ 2 ≤ 0 := le_of_mul_le_mul_left (by simpa only [mul_zero] using hz) (sq_pos_of_pos hba)
  nlinarith [sq_nonneg (d - u)]

theorem support_attractionBranch {Q : Pressure} {a β h u e d : ℝ}
    (hs : pressureSupport Q β (h + β * a * u) e d) :
    pressureSupport (attractionBranch Q a u) β h
      (e + a * u * d - a * u ^ 2 / 2) d := by
  intro β' h' hβ'
  have hc := hs β' (h' + β' * a * u) hβ'
  dsimp [attractionBranch]
  nlinarith [hc]

theorem idealAttraction_eq_of_active {Q : Pressure} {a β h u : ℝ}
    (hu : ActiveShift Q a β h u) :
    idealAttraction Q a β h = attractionBranch Q a u β h := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨u, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hu v⟩

theorem support_of_attractionBranch {Q : Pressure} {a β h u e d : ℝ}
    (hs : pressureSupport (attractionBranch Q a u) β h e d) :
    pressureSupport Q β (h + β * a * u) (e - a * u * d + a * u ^ 2 / 2) d := by
  intro β' h' hβ'
  have hc := hs β' (h' - β' * a * u) hβ'
  dsimp [attractionBranch] at hc
  rw [sub_add_cancel] at hc
  nlinarith [hc]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section InnerSupport

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_supportSet (F : E → ℝ) (D : Set E) (x : E) :
    Convex ℝ (supportSet F D x) := by
  intro v hv w hw a b ha hb hab y hy
  have hv' := hv y hy
  have hw' := hw y hy
  simp only [inner_add_left, real_inner_smul_left]
  calc
    F x + (a * inner ℝ v (y - x) + b * inner ℝ w (y - x)) =
        a * (F x + inner ℝ v (y - x)) + b * (F x + inner ℝ w (y - x)) := by
      calc
        _ = (a + b) * F x +
            (a * inner ℝ v (y - x) + b * inner ℝ w (y - x)) := by rw [hab, one_mul]
        _ = _ := by ring
    _ ≤ a * F y + b * F y := add_le_add
      (mul_le_mul_of_nonneg_left hv' ha) (mul_le_mul_of_nonneg_left hw' hb)
    _ = F y := by rw [← add_mul, hab, one_mul]

theorem isClosed_supportSet (F : E → ℝ) (D : Set E) (x : E) :
    IsClosed (supportSet F D x) := by
  have heq : supportSet F D x = ⋂ y ∈ D, {v | F x + inner ℝ v (y - x) ≤ F y} := by
    ext v
    simp only [supportSet, SupportsOn, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_biInter fun y _ => isClosed_le
    (continuous_const.add (continuous_id.inner continuous_const)) continuous_const

theorem norm_le_of_unit_inner_le (w : E) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z : E, ‖z‖ = 1 → inner ℝ w z ≤ R) : ‖w‖ ≤ R := by
  by_cases hw : w = 0
  · simpa [hw] using hR
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hz : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 := by
    simp [norm_smul, hn]
  have hi : inner ℝ w ((‖w‖⁻¹ : ℝ) • w) = ‖w‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  simpa only [hi] using h _ hz

theorem support_transfer_bound (P Q : E → ℝ) (D : Set E)
    (x c v : E) {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hball : Metric.closedBall x r ⊆ D)
    (happrox : ∀ y ∈ Metric.closedBall x r, |Q y - P y| ≤ δ)
    (hnear : ∀ y ∈ Metric.closedBall x r,
      ∃ w : E, SupportsOn P D y w ∧ ‖w - c‖ ≤ R)
    (hv : SupportsOn Q D x v) :
    ‖v - c‖ ≤ R + 2 * δ / r := by
  apply norm_le_of_unit_inner_le _ (by positivity)
  intro z hz
  let y := x + r • z
  have hy : y ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [y]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz]
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  obtain ⟨w, hw, hwc⟩ := hnear y hy
  have hqy := hv y (hball hy)
  have hpx := hw x (hball hx)
  have hax := (abs_le.mp (happrox x hx)).1
  have hay := (abs_le.mp (happrox y hy)).2
  have hyx : y - x = r • z := by simp [y]
  have hxy : x - y = -(r • z) := by simp [y]
  rw [hyx, real_inner_smul_right] at hqy
  rw [hxy, inner_neg_right, real_inner_smul_right] at hpx
  have hi : inner ℝ (w - c) z ≤ R := by
    calc
      inner ℝ (w - c) z ≤ ‖w - c‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ R := by simpa only [hz, mul_one] using hwc
  rw [inner_sub_left] at hi ⊢
  have hg : r * (inner ℝ v z - inner ℝ c z) ≤ r * R + 2 * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hi hr.le]
  have hd := div_mul_cancel₀ (2 * δ) (ne_of_gt hr)
  nlinarith [hg, hd]

theorem supportSet_nonempty [FiniteDimensional ℝ E] {F : E → ℝ} {D : Set E}
    (hD : IsOpen D) (hF : ConvexOn ℝ D F) {x : E} (hx : x ∈ D) :
    (supportSet F D x).Nonempty := by
  let S : Set (E × ℝ) := {z | z.1 ∈ D ∧ F z.1 < z.2}
  have hSconv : Convex ℝ S := hF.convex_strict_epigraph
  have hFcont : ContinuousOn F D := ConvexOn.continuousOn hD hF
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hDnhds : D ∈ nhds z.1 := hD.mem_nhds hz.1
    have hc : ContinuousAt (fun w : E × ℝ => F w.1) z :=
      (hFcont.continuousAt hDnhds).comp continuous_fst.continuousAt
    exact inter_mem (continuous_fst.continuousAt.preimage_mem_nhds hDnhds)
      (hc.eventually_lt continuous_snd.continuousAt hz.2)
  have hnot : (x, F x) ∉ S := by simp [S]
  obtain ⟨ell, hsep⟩ := geometric_hahn_banach_point_open hSconv hSopen hnot
  let α : ℝ := ell (0, 1)
  let g : E →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (y : E) (r : ℝ) : ell (y, r) = g y + r * α := by
    have hp : (y, r) = (y, 0) + r • (0, 1) := by ext <;> simp
    rw [hp, map_add, map_smul]
    rfl
  have hα : 0 < α := by
    have hh := hsep (x, F x + 1) (by exact ⟨hx, by dsimp; linarith⟩)
    rw [hsplit, hsplit] at hh
    nlinarith
  have hle (y : E) (hy : y ∈ D) : g x + F x * α ≤ g y + F y * α := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hsep (y, F y + ε / α) (by exact ⟨hy, by dsimp; linarith [div_pos hε hα]⟩)
    rw [hsplit, hsplit] at hh
    have he := div_mul_cancel₀ ε (ne_of_gt hα)
    nlinarith [hh, he]
  let v : E := (InnerProductSpace.toDual ℝ E).symm ((-1 / α) • g)
  refine ⟨v, ?_⟩
  intro y hy
  have heq : α * inner ℝ v (y - x) = g x - g y := by
    dsimp [v]
    rw [InnerProductSpace.toDual_symm_apply, smul_apply, map_sub]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hh := hle y hy
  nlinarith [hh, heq]

end InnerSupport

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.EnvelopeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uY

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section CompactEnvelope

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem support_norm_bound {F : E → ℝ} {D : Set E} {x v : E} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hball : Metric.closedBall x r ⊆ D)
    (hbound : ∀ y ∈ Metric.closedBall x r, |F y| ≤ M)
    (hv : SupportsOn F D x v) : ‖v‖ ≤ 2 * M / r := by
  apply norm_le_of_unit_inner_le _ (by positivity)
  intro z hz
  have hy : x + r • z ∈ Metric.closedBall x r := by
    simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr, hz]
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hh := hv (x + r • z) (hball hy)
  simp only [add_sub_cancel_left, real_inner_smul_right] at hh
  have hlo := (abs_le.mp (hbound x hx)).1
  have hhi := (abs_le.mp (hbound _ hy)).2
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem supportsOn_of_tendsto {F : ℕ → E → ℝ} {F₀ : E → ℝ} {D : Set E}
    {x v : ℕ → E} {x₀ v₀ : E}
    (hx : Tendsto x atTop (nhds x₀)) (hv : Tendsto v atTop (nhds v₀))
    (hbase : Tendsto (fun n => F n (x n)) atTop (nhds (F₀ x₀)))
    (hpoint : ∀ y ∈ D, Tendsto (fun n => F n y) atTop (nhds (F₀ y)))
    (hs : ∀ n, SupportsOn (F n) D (x n) (v n)) :
    SupportsOn F₀ D x₀ v₀ := by
  intro y hy
  exact le_of_tendsto_of_tendsto
    (hbase.add (hv.inner (tendsto_const_nhds.sub hx))) (hpoint y hy)
    (Eventually.of_forall fun n => hs n y hy)

theorem continuousOn_tendsto_sequence {X : Type uX} {Y : Type uY} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {S : Set X} (hf : ContinuousOn f S)
    {a : X} (ha : a ∈ S) {s : ℕ → X} (hs : ∀ n, s n ∈ S)
    (hsa : Tendsto s atTop (nhds a)) : Tendsto (fun n => f (s n)) atTop (nhds (f a)) := by
  apply (hf.continuousWithinAt ha).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hsa, Eventually.of_forall hs⟩

theorem supportSet_envelope_closedHull [FiniteDimensional ℝ E]
    {F : ℝ → E → ℝ} {P : E → ℝ} {D : Set E} {K : Set ℝ} {x : E} {r : ℝ}
    (hD : IsOpen D) (hK : IsCompact K) (hr : 0 < r)
    (hball : Metric.closedBall x (2 * r) ⊆ D)
    (hF : ∀ i ∈ K, ConvexOn ℝ D (F i))
    (hFc : ContinuousOn (fun z : ℝ × E => F z.1 z.2) (K ×ˢ D))
    (hPc : ContinuousOn P D)
    (hle : ∀ i ∈ K, ∀ y ∈ D, F i y ≤ P y)
    (hactive : ∀ y ∈ Metric.closedBall x r, ∃ i ∈ K, F i y = P y) :
    supportSet P D x = closure (convexHull ℝ
      {v | ∃ i ∈ K, F i x = P x ∧ SupportsOn (F i) D x v}) := by
  classical
  let G : Set E := {v | ∃ i ∈ K, F i x = P x ∧ SupportsOn (F i) D x v}
  have hx : x ∈ D := hball (Metric.mem_closedBall_self (by positivity))
  have hG : G ⊆ supportSet P D x := by
    rintro v ⟨i, hi, heq, hv⟩ y hy
    rw [← heq]
    exact (hv y hy).trans (hle i hi y hy)
  have hback : closure (convexHull ℝ G) ⊆ supportSet P D x :=
    closure_minimal (convexHull_min hG (convex_supportSet P D x))
      (isClosed_supportSet P D x)
  apply Set.Subset.antisymm ?_ hback
  intro v hv
  by_contra hvout
  obtain ⟨ell, c, hsep, hvc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ G).closure isClosed_closure hvout
  let z : E := (InnerProductSpace.toDual ℝ E).symm ell
  have hell (w : E) : inner ℝ w z = ell w := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨M₀, hM₀⟩ := (hK.prod (isCompact_closedBall x (2 * r))).exists_bound_of_continuousOn
    (hFc.mono (Set.prod_mono Subset.rfl hball))
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  have hbound (i : ℝ) (hi : i ∈ K) (y : E) (hy : y ∈ Metric.closedBall x (2 * r)) :
      |F i y| ≤ M := (hM₀ (i, y) ⟨hi, hy⟩).trans (le_max_right _ _)
  let s : ℕ → ℝ := fun n => (r / (‖z‖ + 1)) * (1 / ((n : ℝ) + 1))
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hsbound (n : ℕ) : s n * ‖z‖ ≤ r := by
    have hn : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hden : 0 < ‖z‖ + 1 := by positivity
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hn
    have hq : r / (‖z‖ + 1) * ‖z‖ ≤ r := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hden).mpr (show r * ‖z‖ ≤ r * (‖z‖ + 1) by nlinarith)
    calc
      s n * ‖z‖ = (r / (‖z‖ + 1) * ‖z‖) * (1 / ((n : ℝ) + 1)) := by dsimp [s]; ring
      _ ≤ (r / (‖z‖ + 1) * ‖z‖) * 1 :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ r := by simpa using hq
  have hs0 : Tendsto s atTop (nhds 0) := by
    simpa [s] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / (‖z‖ + 1))
  let y : ℕ → E := fun n => x + s n • z
  have hymem (n : ℕ) : y n ∈ Metric.closedBall x r := by
    simpa [y, Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos (hspos n)] using hsbound n
  have hyD (n : ℕ) : y n ∈ D :=
    hball (Metric.closedBall_subset_closedBall (by linarith) (hymem n))
  have hy0 : Tendsto y atTop (nhds x) := by
    simpa [y] using tendsto_const_nhds.add (hs0.smul (tendsto_const_nhds (x := z)))
  choose i hi hia using fun n => hactive (y n) (hymem n)
  choose w hw using fun n => supportSet_nonempty hD (hF (i n) (hi n)) (hyD n)
  have hwbound (n : ℕ) : ‖w n‖ ≤ 2 * M / r := by
    have hb : Metric.closedBall (y n) r ⊆ Metric.closedBall x (2 * r) := by
      intro q hq
      apply (dist_triangle q (y n) x).trans
      have hqn := Metric.mem_closedBall.mp hq
      have hyn := Metric.mem_closedBall.mp (hymem n)
      linarith
    exact support_norm_bound hr hM (hb.trans hball)
      (fun q hq => hbound (i n) (hi n) q (hb hq)) (hw n)
  obtain ⟨iw, hiw, σ, hσ, hlim⟩ :=
    (hK.prod (isCompact_closedBall (0 : E) (2 * M / r))).tendsto_subseq
      (x := fun n => (i n, w n)) (fun n => ⟨hi n, by simpa using hwbound n⟩)
  have hiwK : iw.1 ∈ K := hiw.1
  have hilim : Tendsto (fun n => i (σ n)) atTop (nhds iw.1) :=
    continuous_fst.tendsto iw |>.comp hlim
  have hwlim : Tendsto (fun n => w (σ n)) atTop (nhds iw.2) :=
    continuous_snd.tendsto iw |>.comp hlim
  have hylim : Tendsto (fun n => y (σ n)) atTop (nhds x) := hy0.comp hσ.tendsto_atTop
  have hbase : Tendsto (fun n => F (i (σ n)) (y (σ n))) atTop (nhds (F iw.1 x)) :=
    continuousOn_tendsto_sequence hFc (a := (iw.1, x)) ⟨hiwK, hx⟩
      (fun n => ⟨hi (σ n), hyD (σ n)⟩) (hilim.prodMk_nhds hylim)
  have hPbase : Tendsto (fun n => P (y (σ n))) atTop (nhds (P x)) :=
    continuousOn_tendsto_sequence hPc hx (fun n => hyD (σ n)) hylim
  have hia0 : F iw.1 x = P x := by
    apply tendsto_nhds_unique hbase
    simpa only [hia] using hPbase
  have hiws : SupportsOn (F iw.1) D x iw.2 := by
    apply supportsOn_of_tendsto hylim hwlim hbase ?_ (fun n => hw (σ n))
    intro q hq
    exact continuousOn_tendsto_sequence hFc (a := (iw.1, q)) ⟨hiwK, hq⟩
      (fun n => ⟨hi (σ n), hq⟩) (hilim.prodMk_nhds tendsto_const_nhds)
  have hiwG : iw.2 ∈ G := ⟨iw.1, hiwK, hia0, hiws⟩
  have hendpoint (n : ℕ) : inner ℝ v z ≤ inner ℝ (w n) z := by
    have hleft := hv (y n) (hyD n)
    have hright := hw n x hx
    have hdom := hle (i n) (hi n) x hx
    have hyx : y n - x = s n • z := by simp [y]
    have hxy : x - y n = -(s n • z) := by simp [y]
    rw [hyx, real_inner_smul_right] at hleft
    rw [hxy, inner_neg_right, real_inner_smul_right, hia n] at hright
    exact (mul_le_mul_iff_right₀ (hspos n)).mp (by nlinarith [hleft, hright, hdom])
  have hfinal : inner ℝ v z ≤ inner ℝ iw.2 z :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hwlim.inner tendsto_const_nhds)
      (Eventually.of_forall fun n => hendpoint (σ n))
  rw [hell, hell] at hfinal
  have hh := hsep iw.2 (subset_closure (subset_convexHull ℝ G hiwG))
  linarith

end CompactEnvelope

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem dist_lt_one_of_coordinate_half {x y : Position}
    (h : ∀ k : Fin 3, |x k - y k| < 1 / 2) : dist x y < 1 := by
  have hh : dist x y ^ 2 < 1 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hc (k : Fin 3) : dist (x k) (y k) ^ 2 < (1 / 4 : ℝ) := by
      rw [Real.dist_eq]
      have hp := h k
      nlinarith [abs_nonneg (x k - y k)]
    have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      Finset.univ_nonempty (fun k _ => hc k)
    norm_num at hs
    linarith
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem packing_card_bound {L : ℝ} {X : Finset Position} (hX : IsPacking L X) :
    X.card ≤ (⌊2 * L⌋₊ + 1) ^ 3 := by
  classical
  let f : X → (Fin 3 → Fin (⌊2 * L⌋₊ + 1)) := fun x k =>
    ⟨⌊2 * (x : Position) k⌋₊,
      Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [(hX.1 x x.property k).2]))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hne' : (x : Position) ≠ y := fun h => hne (Subtype.ext h)
    have hlo := hX.2 x x.property y y.property hne'
    have hhi : dist (x : Position) y < 1 := by
      apply dist_lt_one_of_coordinate_half
      intro k
      have he : ⌊2 * (x : Position) k⌋₊ = ⌊2 * (y : Position) k⌋₊ :=
        congrArg Fin.val (congrFun hxy k)
      have hx0 := (hX.1 x x.property k).1
      have hy0 := (hX.1 y y.property k).1
      have hxL := Nat.floor_le (show 0 ≤ 2 * (x : Position) k by positivity)
      have hyL := Nat.floor_le (show 0 ≤ 2 * (y : Position) k by positivity)
      have hxU := Nat.lt_floor_add_one (2 * (x : Position) k)
      have hyU := Nat.lt_floor_add_one (2 * (y : Position) k)
      rw [he] at hxL hxU
      apply abs_lt.mpr
      constructor <;> linarith
    linarith
  simpa using Fintype.card_le_of_injective f hf

theorem packing_card_set_bddAbove (L : ℝ) :
    BddAbove {n : ℕ | ∃ X : Finset Position, X.card = n ∧ IsPacking L X} := by
  refine ⟨(⌊2 * L⌋₊ + 1) ^ 3, ?_⟩
  rintro n ⟨X, rfl, hX⟩
  exact packing_card_bound hX

theorem packingNumber_attained (L : ℝ) :
    ∃ X : Finset Position, X.card = packingNumber L ∧ IsPacking L X := by
  exact Nat.sSup_mem (s := {n : ℕ | ∃ X : Finset Position, X.card = n ∧ IsPacking L X})
    ⟨0, ∅, by simp [IsPacking]⟩ (packing_card_set_bddAbove L)

theorem packing_card_le {L : ℝ} {X : Finset Position} (hX : IsPacking L X) :
    X.card ≤ packingNumber L :=
  le_csSup (packing_card_set_bddAbove L) ⟨X, rfl, hX⟩

theorem packingNumber_bound (L : ℝ) :
    packingNumber L ≤ (⌊2 * L⌋₊ + 1) ^ 3 := by
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained L
  simpa only [hcard] using packing_card_bound hX

theorem packingNumber_pos {L : ℝ} (hL : 0 ≤ L) : 0 < packingNumber L := by
  have hh : IsPacking L {0} := by
    constructor
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst x
      intro k
      simp [hL]
    · intro x hx y hy hne
      simp only [Finset.mem_singleton] at hx hy
      exact (hne (hx.trans hy.symm)).elim
  have := packing_card_le hh
  simp only [Finset.card_singleton] at this
  omega

theorem packing_ratio_bound {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ 8 := by
  have hc : (packingNumber s : ℝ) ≤ ((⌊2 * s⌋₊ : ℝ) + 1) ^ 3 := by
    exact_mod_cast packingNumber_bound s
  have hf := Nat.floor_le (show 0 ≤ 2 * s by positivity)
  have hg : ((⌊2 * s⌋₊ : ℝ) + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := by
    gcongr
    linarith
  apply (div_le_iff₀ (by positivity : 0 < (s + 1) ^ 3)).mpr
  nlinarith [hc.trans hg]

theorem packing_ratios_bdd :
    BddAbove {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧ r = (packingNumber s : ℝ) / (s + 1) ^ 3} := by
  refine ⟨8, ?_⟩
  rintro r ⟨s, hs, rfl⟩
  exact packing_ratio_bound hs

theorem packing_ratio_le_density {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ packingDensity :=
  le_csSup packing_ratios_bdd ⟨s, hs, rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have h := packing_ratio_le_density (s := 0) le_rfl
  have hp : (0 : ℝ) < packingNumber 0 := by exact_mod_cast packingNumber_pos (L := 0) le_rfl
  norm_num at h
  exact hp.trans_le h

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.SupportControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uY uI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section MoreSupportGeometry
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem supportsOn_of_local {F : E → ℝ} {D : Set E} {x v : E} {r : ℝ}
    (hF : ConvexOn ℝ D F) (hx : x ∈ D) (hr : 0 < r)
    (hlocal : SupportsOn F (D ∩ Metric.closedBall x r) x v) : SupportsOn F D x v := by
  intro y hy
  let a : ℝ := r / (r + ‖y - x‖ + 1)
  have hd : 0 < r + ‖y - x‖ + 1 := by positivity
  have ha : 0 < a := div_pos hr hd
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith [norm_nonneg (y - x)]
  have hae : a * (r + ‖y - x‖ + 1) = r := div_mul_cancel₀ _ hd.ne'
  have hab : a * ‖y - x‖ ≤ r := by
    nlinarith [mul_nonneg ha.le hr.le]
  let z := (1 - a) • x + a • y
  have hzD : z ∈ D := hF.1 hx hy (sub_nonneg.mpr ha1) ha.le (by ring)
  have hzx : z - x = a • (y - x) := by dsimp [z]; module
  have hzball : z ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact hab
  have hlo := hlocal z ⟨hzD, hzball⟩
  have hhi := hF.2 hx hy (sub_nonneg.mpr ha1) ha.le (show 1 - a + a = 1 by ring)
  change F z ≤ (1 - a) * F x + a * F y at hhi
  rw [hzx, real_inner_smul_right] at hlo
  nlinarith [mul_le_mul_of_nonneg_left (show 0 ≤ (0 : ℝ) from le_rfl) ha.le]

theorem nonempty_of_closedHull_nonempty {G : Set E}
    (h : (closure (convexHull ℝ G)).Nonempty) : G.Nonempty := by
  by_contra hG
  have he : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hG
  simp [he] at h

theorem common_group_of_density_band {Y : Type uY} {I : Type uI}
    (S : Y → Set E) (A : Set Y) (c : I → E) (d : E → ℝ)
    {u R b p : ℝ} (hA : A.Nonempty)
    (hgen : ∀ y ∈ A, S y = closure (convexHull ℝ
      {v | v ∈ S y ∧ ∃ i, v ∈ Metric.closedBall (c i) R}))
    (hne : ∀ y ∈ A, (S y).Nonempty)
    (hband : ∀ y ∈ A, ∀ v ∈ S y, |d v - u| ≤ b)
    (hd : ∀ v w, |d v - d w| ≤ dist v w)
    (hsep : ∀ i j, i ≠ j → p ≤ |d (c i) - d (c j)|)
    (hgap : 2 * (b + R) < p) :
    ∃ i, ∀ y ∈ A, S y ⊆ Metric.closedBall (c i) R := by
  classical
  have hcenter (y : Y) (hy : y ∈ A) (v : E) (hv : v ∈ S y)
      (i : I) (hi : v ∈ Metric.closedBall (c i) R) : |d (c i) - u| ≤ b + R := by
    have hdist : |d (c i) - d v| ≤ R := by
      calc
        _ ≤ dist (c i) v := hd _ _
        _ = dist v (c i) := dist_comm _ _
        _ ≤ R := hi
    calc
      |d (c i) - u| ≤ |d (c i) - d v| + |d v - u| := abs_sub_le _ _ _
      _ ≤ b + R := by linarith [hband y hy v hv]
  obtain ⟨y₀, hy₀⟩ := hA
  have hng : ({v | v ∈ S y₀ ∧ ∃ i, v ∈ Metric.closedBall (c i) R}).Nonempty := by
    apply nonempty_of_closedHull_nonempty
    rw [← hgen y₀ hy₀]
    exact hne y₀ hy₀
  obtain ⟨v₀, hv₀, i₀, hi₀⟩ := hng
  have hc₀ := hcenter y₀ hy₀ v₀ hv₀ i₀ hi₀
  refine ⟨i₀, ?_⟩
  intro y hy
  rw [hgen y hy]
  apply closure_minimal _ Metric.isClosed_closedBall
  apply convexHull_min _ (convex_closedBall (c i₀) R)
  rintro v ⟨hv, i, hi⟩
  have heq : i = i₀ := by
    by_contra hne'
    have hc := hcenter y hy v hv i hi
    have habs : |d (c i) - d (c i₀)| ≤ 2 * (b + R) := by
      calc
        _ ≤ |d (c i) - u| + |u - d (c i₀)| := abs_sub_le _ _ _
        _ = |d (c i) - u| + |d (c i₀) - u| := by rw [abs_sub_comm u]
        _ ≤ 2 * (b + R) := by linarith
    linarith [hsep i i₀ hne']
  simpa [heq] using hi

end MoreSupportGeometry

theorem active_neighborhood_density_band {P Q : Pressure}
    {a β h u βy hy e d η δ C r : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβy : 0 < βy) (hη : 0 < η)
    (hu : ActiveShift Q a β h u) (hs : pressureSupport P βy hy e d)
    (happrox : ∀ z ∈ ({0, η, -η} : Set ℝ),
      |Q β (h + β * a * u + z) - P β (h + β * a * u + z)| ≤ δ)
    (hlip : ∀ z ∈ ({0, η, -η} : Set ℝ),
      |P βy (hy + z) - P β (h + β * a * u + z)| ≤ C * r) :
    |d - u| ≤ η / (2 * β * a) + 2 * δ / η + 2 * C * r / η := by
  have hzero : (0 : ℝ) ∈ ({0, η, -η} : Set ℝ) := by simp
  have hplus : η ∈ ({0, η, -η} : Set ℝ) := by simp
  have hminus : -η ∈ ({0, η, -η} : Set ℝ) := by simp
  have happ0 := happrox 0 hzero
  have hlip0 := hlip 0 hzero
  simp only [add_zero] at happ0 hlip0
  have hsupport (z : ℝ) : z * d ≤ P βy (hy + z) - P βy hy := by
    have hh := hs βy (hy + z) hβy
    simp only [sub_self, mul_zero, add_zero, add_sub_cancel_left] at hh
    nlinarith
  have hup : η * (d - u) ≤ η ^ 2 / (2 * β * a) + 2 * δ + 2 * C * r := by
    have hp := active_parabola ha hβ hu η
    have hq := hsupport η
    have ha := abs_le.mp (happrox η hplus)
    have hl := abs_le.mp (hlip η hplus)
    have ha0 := abs_le.mp happ0
    have hl0 := abs_le.mp hlip0
    linarith
  have hlo : -(η * (d - u)) ≤ η ^ 2 / (2 * β * a) + 2 * δ + 2 * C * r := by
    have hp := active_parabola ha hβ hu (-η)
    have hq := hsupport (-η)
    have ha := abs_le.mp (happrox (-η) hminus)
    have hl := abs_le.mp (hlip (-η) hminus)
    have ha0 := abs_le.mp happ0
    have hl0 := abs_le.mp hlip0
    simp only [neg_sq] at hp
    linarith
  have heq : η * (η / (2 * β * a) + 2 * δ / η + 2 * C * r / η) =
      η ^ 2 / (2 * β * a) + 2 * δ + 2 * C * r := by
    field_simp
  apply abs_le.mpr
  constructor <;> nlinarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.FamilyIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma ideal_bddAbove_of_active {Q : Pressure} {a β h u : ℝ} (hu : ActiveShift Q a β h u) :
    BddAbove (range fun v => attractionBranch Q a v β h) :=
  ⟨attractionBranch Q a u β h, fun _ ⟨v, hv⟩ => hv ▸ hu v⟩

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.ParameterPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma parameter_inner (x y : Parameter) : inner ℝ x y = x 0*y 0+x 1*y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma parameter_coord_abs_le (x : Parameter) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2:ℝ≥0∞)) x i

lemma parameter_norm_le (x : Parameter) : ‖x‖ ≤ |x 0|+|x 1| := by
  have hh : ‖x‖^2 = |x 0|^2+|x 1|^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  nlinarith [norm_nonneg x, abs_nonneg (x 0), abs_nonneg (x 1),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

lemma continuous_parameter {X : Type uX} [TopologicalSpace X] (β h : X → ℝ) (hβ : Continuous β) (hh : Continuous h) :
    Continuous (fun x => parameter (β x) (h x)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact hβ
  · exact hh

lemma isOpen_positiveParameters : IsOpen positiveParameters := by
  exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (0:Fin 2))

lemma convex_positiveParameters : Convex ℝ positiveParameters := by
  intro x hx y hy a b ha hb hab
  change 0 < a*x 0+b*y 0
  have hh := lt_min (show 0 < x 0 from hx) (show 0 < y 0 from hy)
  have hm := mul_pos (show 0 < a+b by linarith) hh
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (x 0) (y 0)) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right (x 0) (y 0)) hb
  nlinarith

lemma pressureSupport_iff {Q : Pressure} {x v : Parameter} :
    pressureSupport Q (x 0) (x 1) (v 0) (v 1) ↔
      SupportsOn (onParameters Q) positiveParameters x v := by
  constructor
  · intro hs y hy
    have hh := hs (y 0) (y 1) hy
    simpa only [onParameters, parameter_inner, PiLp.sub_apply, add_assoc] using hh
  · intro hs β h hβ
    have hh := hs (parameter β h) hβ
    simpa only [onParameters, parameter_inner, PiLp.sub_apply, parameter_zero, parameter_one, add_assoc] using hh

lemma convexOn_attractionBranch {Q : Pressure} (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (a u : ℝ) : ConvexOn ℝ positiveParameters (onParameters (attractionBranch Q a u)) := by
  refine ⟨convex_positiveParameters, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hh := hQ.2 (show parameter (x 0) (x 1+x 0*a*u) ∈ positiveParameters from hx)
    (show parameter (y 0) (y 1+y 0*a*u) ∈ positiveParameters from hy) hc hd hcd
  have he : c • parameter (x 0) (x 1+x 0*a*u)+d • parameter (y 0) (y 1+y 0*a*u) =
      parameter (c*x 0+d*y 0) (c*x 1+d*y 1+(c*x 0+d*y 0)*a*u) := by
    ext i
    fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply]; ring
  rw [he] at hh
  dsimp only [onParameters, attractionBranch, parameter_zero, parameter_one] at hh ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hh ⊢
  nlinarith

lemma convexOn_idealAttraction {Q : Pressure} (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    {a : ℝ} (hactive : ∀ β h, 0 < β → ∃ u, ActiveShift Q a β h u) :
    ConvexOn ℝ positiveParameters (onParameters (idealAttraction Q a)) := by
  refine ⟨convex_positiveParameters, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hz := convex_positiveParameters hx hy hc hd hcd
  obtain ⟨u, hu⟩ := hactive _ _ hz
  obtain ⟨v, hv⟩ := hactive _ _ hx
  obtain ⟨w, hw⟩ := hactive _ _ hy
  have hh := (convexOn_attractionBranch hQ a u).2 hx hy hc hd hcd
  change idealAttraction Q a _ _ ≤ c*idealAttraction Q a _ _+d*idealAttraction Q a _ _
  rw [idealAttraction_eq_of_active hu, idealAttraction_eq_of_active hv, idealAttraction_eq_of_active hw]
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hv u) hc) (mul_le_mul_of_nonneg_left (hw u) hd))

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.IdealLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma finiteMax_le {ι : Type uIndex} [Fintype ι] [Nonempty ι] (f : ι → ℝ) {c : ℝ}
    (hc : ∀ i, f i ≤ c) : finiteMax f ≤ c := csSup_le (range_nonempty f) (by rintro _ ⟨i,rfl⟩; exact hc i)
lemma le_finiteMax {ι : Type uIndex} [Fintype ι] (f : ι → ℝ) (i : ι) : f i ≤ finiteMax f :=
  le_csSup (Finite.bddAbove_range f) (mem_range_self i)
lemma finiteMax_attained {ι : Type uIndex} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ∃ i, finiteMax f = f i := by
  obtain ⟨i, hi⟩ := Finite.exists_max f
  exact ⟨i, le_antisymm (finiteMax_le f hi) (le_finiteMax f i)⟩

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.IdealSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma branch_joint_continuous {Q : Pressure}
    (hQ : ContinuousOn (onParameters Q) positiveParameters) (a : ℝ) :
    ContinuousOn (fun z : ℝ × Parameter => onParameters (attractionBranch Q a z.1) z.2)
      (univ ×ˢ positiveParameters) := by
  have hc0 : Continuous (fun z : ℝ × Parameter => z.2 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_snd
  have hc1 : Continuous (fun z : ℝ × Parameter => z.2 1) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_snd
  have hmap : Continuous (fun z : ℝ × Parameter => parameter (z.2 0) (z.2 1+z.2 0*a*z.1)) :=
    continuous_parameter _ _ hc0 (hc1.add ((hc0.mul_const a).mul continuous_fst))
  have hcomp := hQ.comp (s := univ ×ˢ positiveParameters) hmap.continuousOn (by
    intro z hz
    change 0 < z.2 0
    exact hz.2)
  exact hcomp.sub (((hc0.mul_const a).div_const 2).mul (continuous_fst.pow 2)).continuousOn

lemma ideal_supportSet_generated {Q : Pressure} {a U r : ℝ} {x : Parameter}
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q)) (ha : 0 < a)
    (hactive : ∀ β h, 0 < β → ∃ u, ActiveShift Q a β h u)
    (hr : 0 < r) (hxr : 2*r < x 0)
    (hlocal : ∀ y ∈ Metric.closedBall x r, ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a (y 0) (y 1) u) :
    supportSet (onParameters (idealAttraction Q a)) positiveParameters x =
      closure (convexHull ℝ {v : Parameter | ∃ u ∈ Icc (0:ℝ) U,
        ActiveShift Q a (x 0) (x 1) u ∧ ∃ e : ℝ,
        pressureSupport Q (x 0) (x 1+x 0*a*u) e u ∧ v=parameter (e+a*u^2/2) u}) := by
  have hball : Metric.closedBall x (2*r) ⊆ positiveParameters := by
    intro y hy
    have hcoord := parameter_coord_abs_le (y-x) 0
    have hn := Metric.mem_closedBall.mp hy
    rw [dist_eq_norm] at hn
    simp only [PiLp.sub_apply] at hcoord
    have hh := (abs_le.mp (hcoord.trans hn)).1
    change 0 < y 0
    linarith
  have hx : 0 < x 0 := by linarith
  have hP := convexOn_idealAttraction hQ hactive
  have hformula := supportSet_envelope_closedHull isOpen_positiveParameters isCompact_Icc hr hball
    (fun u _ => convexOn_attractionBranch hQ a u)
    ((branch_joint_continuous (hQ.continuousOn isOpen_positiveParameters) a).mono
      (prod_mono (subset_univ _) Subset.rfl))
    (hP.continuousOn isOpen_positiveParameters)
    (fun u _ y hy => by
      obtain ⟨v, hv⟩ := hactive (y 0) (y 1) hy
      change attractionBranch Q a u (y 0) (y 1) ≤ idealAttraction Q a (y 0) (y 1)
      rw [idealAttraction_eq_of_active hv]
      exact hv u)
    (fun y hy => by
      obtain ⟨u, hub, hu⟩ := hlocal y hy
      exact ⟨u, hub, (idealAttraction_eq_of_active hu).symm⟩)
  rw [hformula]
  congr 2
  ext v
  constructor
  · rintro ⟨u, hub, heq, hv⟩
    have hu : ActiveShift Q a (x 0) (x 1) u := by
      intro w
      change attractionBranch Q a u (x 0) (x 1) = idealAttraction Q a (x 0) (x 1) at heq
      rw [heq]
      obtain ⟨z, hz⟩ := hactive (x 0) (x 1) hx
      exact le_csSup (ideal_bddAbove_of_active hz) (mem_range_self w)
    have hs := support_of_attractionBranch (pressureSupport_iff.mpr hv)
    have hd := active_support_density ha hx hu hs
    refine ⟨u, hub, hu, v 0-a*u*(v 1)+a*u^2/2, ?_, ?_⟩
    · simpa only [hd] using hs
    · ext i
      fin_cases i
      · change v 0 = v 0-a*u*(v 1)+a*u^2/2+a*u^2/2
        rw [hd]
        ring
      · change v 1 = u
        exact hd
  · rintro ⟨u, hub, hu, e, hs, rfl⟩
    refine ⟨u, hub, (idealAttraction_eq_of_active hu).symm, ?_⟩
    have hs' : pressureSupport (attractionBranch Q a u) (x 0) (x 1) (e+a*u^2/2) u := by
      convert support_attractionBranch hs using 1
      ring
    exact pressureSupport_iff.mp hs'

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.InitialSlopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma phase_groups_of_generators {Q : Pressure} {x : Parameter} {G : Set Parameter} {r : ℝ}
    (hgen : supportSet (onParameters Q) positiveParameters x=closure (convexHull ℝ G))
    (hG : ∀ v ∈ G, ∃ i : Fin 3, v ∈ Metric.closedBall (phaseSlope i) r) :
    HasPhaseGroups Q x r := by
  apply le_antisymm
  · rw [hgen]
    apply closure_mono
    apply convexHull_mono
    intro v hv
    refine ⟨?_, hG v hv⟩
    exact subset_closure (subset_convexHull ℝ G hv)
  · apply closure_minimal _ (isClosed_supportSet _ _ _)
    exact convexHull_min (fun _ h => h.1) (convex_supportSet _ _ _)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.ParameterTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma phaseWindow_coords {x : Parameter} {r : ℝ} (hx : x ∈ phaseWindow r) :
    |x 0-1| ≤ r ∧ |x 1+3/4| ≤ r := by
  have hn : ‖x-phaseCenter‖ ≤ r := Metric.mem_closedBall.mp hx
  constructor
  · exact (parameter_coord_abs_le (x-phaseCenter) 0).trans hn
  · have hh := (parameter_coord_abs_le (x-phaseCenter) 1).trans hn
    change |x 1-(-3/4)| ≤ r at hh
    simpa only [neg_div, sub_neg_eq_add] using hh

lemma phaseWindow_positive {x : Parameter} {r : ℝ} (hr : r < 1) (hx : x ∈ phaseWindow r) :
    x ∈ positiveParameters := by
  have hh := (abs_le.mp (phaseWindow_coords hx).1).1
  change 0 < x 0
  linarith

lemma phaseWindow_mono {r s : ℝ} (h : r ≤ s) : phaseWindow r ⊆ phaseWindow s :=
  Metric.closedBall_subset_closedBall h

lemma phaseWindow_near {x y : Parameter} {r s : ℝ} (hx : x ∈ phaseWindow r)
    (hy : y ∈ Metric.closedBall x s) : y ∈ phaseWindow (r+s) := by
  change dist y phaseCenter ≤ r+s
  calc
    dist y phaseCenter ≤ dist y x+dist x phaseCenter := dist_triangle _ _ _
    _ ≤ r+s := by have h1 := Metric.mem_closedBall.mp hx; have h2 := Metric.mem_closedBall.mp hy; linarith

lemma phaseWindow_quarter_bounds {x : Parameter} (hx : x ∈ phaseWindow (1/4)) :
    x 0 ∈ Icc (3/4:ℝ) (5/4) ∧ |x 1| ≤ 2 := by
  have h1 := abs_le.mp (phaseWindow_coords hx).1
  have h2 := abs_le.mp (phaseWindow_coords hx).2
  constructor
  · constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

lemma parameter_vertical_norm (h : ℝ) : ‖parameter 0 h‖ = |h| := by
  have hn := parameter_norm_le (parameter 0 h)
  have hl := parameter_coord_abs_le (parameter 0 h) 1
  simp only [parameter_zero, parameter_one, abs_zero, zero_add] at hn hl
  exact le_antisymm hn hl

lemma parameter_horizontal_norm (β : ℝ) : ‖parameter β 0‖ = |β| := by
  have hn := parameter_norm_le (parameter β 0)
  have hl := parameter_coord_abs_le (parameter β 0) 0
  simp only [parameter_zero, parameter_one, abs_zero, add_zero] at hn hl
  exact le_antisymm hn hl

lemma parameter_sub (β h β' h' : ℝ) : parameter β h-parameter β' h'=parameter (β-β') (h-h') := by
  ext i
  fin_cases i <;> rfl

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PhaseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma phaseSlope_zero : phaseSlope 0=parameter 0 0 := by simp [phaseSlope,phaseDensity]
lemma phaseSlope_one : phaseSlope 1=parameter (3*packingDensity/4) packingDensity := by
  simp only [phaseSlope, phaseDensity, Matrix.cons_val_one, Matrix.cons_val_zero]
  congr 1
  dsimp [phaseMass]
  field_simp
  ring
lemma phaseSlope_two : phaseSlope 2=parameter (12*packingDensity) (4*packingDensity) := by
  change parameter (phaseMass/2*(4*packingDensity)^2) (4*packingDensity)=_
  congr 1
  dsimp [phaseMass]
  field_simp
  ring

lemma phase_densities_separated (i j : Fin 3) (hij : i ≠ j) :
    packingDensity ≤ |phaseSlope i 1-phaseSlope j 1| := by
  have hp := packingDensity_pos
  fin_cases i <;> fin_cases j <;> simp_all [phaseSlope_zero,phaseSlope_one,phaseSlope_two,abs_of_pos,abs_of_neg] <;>
    linarith

lemma phaseRadius_pos : 0 < phaseRadius := div_pos packingDensity_pos (by norm_num)
lemma pressureRadius_pos : 0 < pressureRadius := div_pos packingDensity_pos (by norm_num)

lemma directional_lower (z : Parameter) : packingDensity/8*‖z‖ ≤ directionalMax z := by
  let m := directionalMax z
  let A := inner ℝ (phaseSlope 0-targetSlope) z
  let B := inner ℝ (phaseSlope 1-targetSlope) z
  let C := inner ℝ (phaseSlope 2-targetSlope) z
  have hA : A ≤ m := le_finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z) 0
  have hB : B ≤ m := le_finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z) 1
  have hC : C ≤ m := le_finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z) 2
  have hsum : A+B+C=0 := by
    dsimp [A,B,C]
    rw [phaseSlope_zero,phaseSlope_one,phaseSlope_two]
    simp only [parameter_inner, PiLp.sub_apply, parameter_zero,parameter_one,targetSlope]
    ring
  have hm : 0 ≤ m := by linarith
  have hAl : -2*m ≤ A := by linarith
  have hBl : -2*m ≤ B := by linarith
  have hCl : -2*m ≤ C := by linarith
  have hcoord₀ : |packingDensity*z 0| ≤ 2*m := by
    dsimp [A,B,C] at hA hB hC hAl hBl hCl
    rw [phaseSlope_zero] at hA hAl
    rw [phaseSlope_one] at hB hBl
    rw [phaseSlope_two] at hC hCl
    simp only [parameter_inner, PiLp.sub_apply, parameter_zero,parameter_one,targetSlope] at hA hB hC hAl hBl hCl
    rw [abs_le]
    constructor <;> nlinarith
  have hcoord₁ : |packingDensity*z 1| ≤ 5*m := by
    dsimp [A,B,C] at hA hB hC hAl hBl hCl
    rw [phaseSlope_zero] at hA hAl
    rw [phaseSlope_one] at hB hBl
    rw [phaseSlope_two] at hC hCl
    simp only [parameter_inner, PiLp.sub_apply, parameter_zero,parameter_one,targetSlope] at hA hB hC hAl hBl hCl
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_mul,abs_of_pos packingDensity_pos] at hcoord₀ hcoord₁
  have hn := mul_le_mul_of_nonneg_left (parameter_norm_le z) packingDensity_pos.le
  change packingDensity/8*‖z‖ ≤ m
  nlinarith

lemma mem_closedHull_of_inner_le {G : Set Parameter} {v : Parameter}
    (h : ∀ z : Parameter, ∃ w ∈ G, inner ℝ v z ≤ inner ℝ w z) :
    v ∈ closure (convexHull ℝ G) := by
  by_contra hv
  obtain ⟨ell,c,hsep,hvc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ G).closure isClosed_closure hv
  let z : Parameter := (InnerProductSpace.toDual ℝ Parameter).symm ell
  have hell (w : Parameter) : inner ℝ w z=ell w := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨w,hw,hh⟩ := h z
  have hs := hsep w (subset_closure (subset_convexHull ℝ G hw))
  rw [hell,hell] at hh
  linarith

lemma robust_phase_triangle (w : Fin 3 → Parameter)
    (hw : ∀ i, w i ∈ Metric.closedBall (phaseSlope i) phaseRadius) :
    Metric.closedBall targetSlope pressureRadius ⊆ closure (convexHull ℝ (range w)) := by
  intro v hv
  apply mem_closedHull_of_inner_le
  intro z
  obtain ⟨i,hi⟩ := finiteMax_attained (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z)
  have hd := directional_lower z
  change directionalMax z=inner ℝ (phaseSlope i-targetSlope) z at hi
  rw [hi] at hd
  have hvn : ‖v-targetSlope‖ ≤ pressureRadius := Metric.mem_closedBall.mp hv
  have hwn : ‖phaseSlope i-w i‖ ≤ phaseRadius := by
    rw [norm_sub_rev]
    exact Metric.mem_closedBall.mp (hw i)
  have hvz := (real_inner_le_norm (v-targetSlope) z).trans (mul_le_mul_of_nonneg_right hvn (norm_nonneg z))
  have hwz := (real_inner_le_norm (phaseSlope i-w i) z).trans (mul_le_mul_of_nonneg_right hwn (norm_nonneg z))
  refine ⟨w i, mem_range_self i, ?_⟩
  rw [inner_sub_left] at hd hvz hwz
  dsimp [pressureRadius,phaseRadius] at hvz hwz
  nlinarith [mul_nonneg packingDensity_pos.le (norm_nonneg z)]

lemma exclusionNormal_norm (i : Fin 3) : ‖exclusionNormal i‖ ≤ 5 := by
  have hn := parameter_norm_le (exclusionNormal i)
  fin_cases i <;> norm_num [exclusionNormal] at hn ⊢ <;> linarith

lemma exclusion_gap (i j : Fin 3) (hij : j ≠ i) :
    inner ℝ (phaseSlope j) (exclusionNormal i)+3*packingDensity/4 ≤ inner ℝ targetSlope (exclusionNormal i) := by
  have hp := packingDensity_pos
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [phaseSlope,phaseDensity,phaseMass,exclusionNormal,parameter_inner,targetSlope]
  all_goals field_simp
  all_goals nlinarith

lemma exclusion_ball (i j : Fin 3) (hij : j ≠ i) {v : Parameter}
    (hv : v ∈ Metric.closedBall (phaseSlope j) phaseRadius) :
    inner ℝ v (exclusionNormal i) ≤ inner ℝ targetSlope (exclusionNormal i)-packingDensity/2 := by
  have hn : ‖v-phaseSlope j‖ ≤ phaseRadius := Metric.mem_closedBall.mp hv
  have hh := (real_inner_le_norm (v-phaseSlope j) (exclusionNormal i)).trans
    (mul_le_mul hn (exclusionNormal_norm i) (norm_nonneg _) phaseRadius_pos.le)
  rw [inner_sub_left] at hh
  have hg := exclusion_gap i j hij
  dsimp [phaseRadius] at hh
  linarith [packingDensity_pos]

lemma phase_plane_at_center (i : Fin 3) : limitingPlane i 1 (-3/4)=0 := by
  have hp := packingDensity_pos.ne'
  fin_cases i <;> dsimp [limitingPlane,phaseDensity,phaseOffset,phaseMass] <;> field_simp <;> ring

lemma phase_plane_difference (i : Fin 3) (x : Parameter) :
    limitingPlane i (x 0) (x 1)=inner ℝ (phaseSlope i) (x-phaseCenter) := by
  have hh := phase_plane_at_center i
  dsimp [limitingPlane] at hh ⊢
  simp only [phaseSlope,phaseCenter,parameter_inner,PiLp.sub_apply,parameter_zero,parameter_one]
  nlinarith

lemma threePlane_center : onParameters threePlane phaseCenter=0 := by
  change finiteMax (fun i => limitingPlane i 1 (-3/4))=0
  apply le_antisymm
  · apply finiteMax_le
    intro i
    rw [phase_plane_at_center]
  · have hh := le_finiteMax (fun i => limitingPlane i 1 (-3/4)) (0:Fin 3)
    rw [phase_plane_at_center] at hh
    exact hh

lemma threePlane_growth (x : Parameter) :
    pressureRadius*‖x-phaseCenter‖ ≤ onParameters threePlane x-onParameters threePlane phaseCenter-
      inner ℝ targetSlope (x-phaseCenter) := by
  rw [threePlane_center,sub_zero]
  obtain ⟨i,hi⟩ := finiteMax_attained (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) (x-phaseCenter))
  have hd := directional_lower (x-phaseCenter)
  change directionalMax (x-phaseCenter)=_ at hi
  rw [hi,inner_sub_left] at hd
  have hh := le_finiteMax (fun i => limitingPlane i (x 0) (x 1)) i
  rw [phase_plane_difference] at hh
  change inner ℝ (phaseSlope i) (x-phaseCenter) ≤ onParameters threePlane x at hh
  dsimp [pressureRadius]
  nlinarith [mul_nonneg packingDensity_pos.le (norm_nonneg (x-phaseCenter))]

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.PressureBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma support_ball_of_groups {Q : Pressure} {x : Parameter} {r : ℝ}
    (hgroup : HasPhaseGroups Q x r) (hr : r ≤ phaseRadius)
    (hg : targetSlope ∈ supportSet (onParameters Q) positiveParameters x) :
    Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters Q) positiveParameters x := by
  classical
  let S := supportSet (onParameters Q) positiveParameters x
  have hex (i : Fin 3) : ∃ w ∈ S, w ∈ Metric.closedBall (phaseSlope i) phaseRadius := by
    by_contra hn
    let n := exclusionNormal i
    let c := inner ℝ targetSlope n-packingDensity/2
    let H : Set Parameter := {v | inner ℝ v n ≤ c}
    have hc : Convex ℝ H := by
      intro v hv w hw a b ha hb hab
      change inner ℝ (a • v+b • w) n ≤ c
      rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
      have hh := add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
      calc
        _ ≤ a*c+b*c := hh
        _ = c := by rw [← add_mul,hab,one_mul]
    have hclosed : IsClosed H := isClosed_le (continuous_id.inner continuous_const) continuous_const
    have hSH : S ⊆ H := by
      change supportSet (onParameters Q) positiveParameters x ⊆ H
      rw [hgroup]
      apply closure_minimal _ hclosed
      apply convexHull_min _ hc
      rintro v ⟨hv,j,hj⟩
      have hj' := Metric.closedBall_subset_closedBall hr hj
      have hij : j ≠ i := by
        intro heq
        exact hn ⟨v,hv,heq ▸ hj'⟩
      exact exclusion_ball i j hij hj'
    have hh := hSH hg
    change inner ℝ targetSlope n ≤ inner ℝ targetSlope n-packingDensity/2 at hh
    linarith [packingDensity_pos]
  choose w hw hwball using hex
  intro v hv
  have htri := robust_phase_triangle w hwball hv
  have hsub : closure (convexHull ℝ (range w)) ⊆ S := by
    apply closure_minimal _ (isClosed_supportSet _ _ _)
    apply convexHull_min _ (convex_supportSet _ _ _)
    rintro _ ⟨i,rfl⟩
    exact hw i
  exact hsub htri

lemma pressure_ball_exists {Q : Pressure}
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (hclose : ∀ x ∈ phaseWindow (1/8), |onParameters Q x-onParameters threePlane x| ≤ pressureRadius/32)
    (hgroups : ∀ x ∈ phaseWindow (1/8), ∃ r ≤ phaseRadius, HasPhaseGroups Q x r) :
    ∃ x ∈ Metric.ball phaseCenter (1/8),
      Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters Q) positiveParameters x := by
  have hW : phaseWindow (1/8) ⊆ positiveParameters := by
    intro x hx
    exact phaseWindow_positive (by norm_num) hx
  have hQc := hQ.continuousOn isOpen_positiveParameters
  let F : Parameter → ℝ := fun x => onParameters Q x-inner ℝ targetSlope x
  have hFc : ContinuousOn F (phaseWindow (1/8)) :=
    (hQc.mono hW).sub (continuous_const.inner continuous_id).continuousOn
  have hcenter : phaseCenter ∈ phaseWindow (1/8) := Metric.mem_closedBall_self (by norm_num)
  obtain ⟨x,hx,hmin⟩ := (isCompact_closedBall phaseCenter (1/8)).exists_isMinOn ⟨phaseCenter,hcenter⟩ hFc
  have hdist : dist x phaseCenter < 1/8 := by
    by_contra hh
    have hxbound := Metric.mem_closedBall.mp hx
    have heq : dist x phaseCenter=1/8 := le_antisymm hxbound (le_of_not_gt hh)
    have hgrow := threePlane_growth x
    rw [← dist_eq_norm,heq] at hgrow
    have ha := abs_le.mp (hclose x hx)
    have hb := abs_le.mp (hclose phaseCenter hcenter)
    have hm := hmin hcenter
    dsimp [F] at hm
    rw [inner_sub_right] at hgrow
    linarith [pressureRadius_pos]
  have hg : targetSlope ∈ supportSet (onParameters Q) positiveParameters x := by
    apply supportsOn_of_local hQ (hW hx) (sub_pos.mpr hdist)
    intro y hy
    have hyW : y ∈ phaseWindow (1/8) := by
      change dist y phaseCenter ≤ 1/8
      calc
        _ ≤ dist y x+dist x phaseCenter := dist_triangle _ _ _
        _ ≤ 1/8 := by have ht := Metric.mem_closedBall.mp hy.2; linarith
    have hm := hmin hyW
    dsimp [F] at hm
    rw [inner_sub_right]
    linarith
  obtain ⟨r,hr,hgrp⟩ := hgroups x hx
  exact ⟨x,hdist,support_ball_of_groups hgrp hr hg⟩

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.Propagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma parameter_shift_dist (x y : Parameter) (z : ℝ) :
    dist (parameter (x 0) (x 1+z)) (parameter (y 0) (y 1+z))=dist x y := by
  rw [dist_eq_norm,parameter_sub,dist_eq_norm]
  congr 1
  ext i
  fin_cases i <;> simp

lemma parameter_shift_dist_self (x : Parameter) (z : ℝ) :
    dist (parameter (x 0) (x 1+z)) x=|z| := by
  rw [← parameter_eta x,dist_eq_norm,parameter_sub]
  simp only [parameter_zero,parameter_one,sub_self,add_sub_cancel_left]
  exact parameter_vertical_norm z

lemma propagate_phase_groups {P Q : Pressure} {a δ C U k l r s : ℝ}
    (hP : ConvexOn ℝ positiveParameters (onParameters P))
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (ha : 0 < a) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hk : 0 < k) (hl : 0 < l) (hr : 0 ≤ r) (hs : s ≤ 1/4)
    (hgap : 2*(k+2*δ/(k*a)+2*C*l/k+r)<packingDensity)
    (hgroups : ∀ y ∈ phaseWindow s, HasPhaseGroups P y r)
    (happ : ∀ y ∈ phaseWindow (1/4), |onParameters Q y-onParameters P y| ≤ δ)
    (hlip : ∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
      |onParameters P x-onParameters P y| ≤ C*dist x y)
    (hact : ∀ β h, 0 < β → ∃ u, ActiveShift Q a β h u)
    (hcut : ∀ x ∈ phaseWindow (1/2), ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a (x 0) (x 1) u) :
    ∀ w ∈ phaseWindow (s-(5/4*U+k+l+1)*a),
      HasPhaseGroups (idealAttraction Q a) w (r+2*δ/(l*a)+a*U^2/2) := by
  intro w hw
  let S := 5/4*U+k+l+1
  have hS : 0 < S := by dsimp [S]; positivity
  have hwq : w ∈ phaseWindow (1/4) := phaseWindow_mono (by dsimp [S] at hS; nlinarith) hw
  obtain ⟨hwβ, _⟩ := phaseWindow_quarter_bounds hwq
  have hwβ0 : 0 < w 0 := by linarith [hwβ.1]
  have hlocal : ∀ y ∈ Metric.closedBall w (1/16), ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a (y 0) (y 1) u := by
    intro y hy
    exact hcut y (phaseWindow_mono (by norm_num : (1/4:ℝ)+1/16≤1/2) (phaseWindow_near hwq hy))
  have hgen := ideal_supportSet_generated hQ ha hact (by norm_num : (0:ℝ)<1/16)
    (by linarith [hwβ.1] : 2*(1/16:ℝ)<w 0) hlocal
  apply phase_groups_of_generators hgen
  rintro v ⟨u, hub, hu, e, he, rfl⟩
  let x := parameter (w 0) (w 1+w 0*a*u)
  have hxu : dist x w ≤ 5/4*U*a := by
    rw [parameter_shift_dist_self,abs_of_nonneg (by exact mul_nonneg (mul_nonneg hwβ0.le ha.le) hub.1 : 0 ≤ w 0*a*u)]
    have hm := mul_le_mul hwβ.2 hub.2 hub.1 (by norm_num : (0:ℝ)≤5/4)
    nlinarith [mul_le_mul_of_nonneg_right hm ha.le]
  have htest (y : Parameter) (hy : y ∈ Metric.closedBall x (l*a)) (z : ℝ) (hz : |z| ≤ k*a) :
      parameter (y 0) (y 1+z) ∈ phaseWindow s := by
    change dist (parameter (y 0) (y 1+z)) phaseCenter ≤ s
    have h1 := dist_triangle (parameter (y 0) (y 1+z)) y phaseCenter
    rw [parameter_shift_dist_self] at h1
    have h2 := dist_triangle y x phaseCenter
    have h3 := dist_triangle x w phaseCenter
    have hy' := Metric.mem_closedBall.mp hy
    have hw' := Metric.mem_closedBall.mp hw
    change dist w phaseCenter ≤ s-S*a at hw'
    dsimp [S] at hw'
    nlinarith
  have hbase (y : Parameter) (hy : y ∈ Metric.closedBall x (l*a)) : y ∈ phaseWindow s := by
    have hh := htest y hy 0 (by simp; positivity)
    simpa only [add_zero,parameter_eta] using hh
  have hbaseq (y : Parameter) (hy : y ∈ Metric.closedBall x (l*a)) : y ∈ phaseWindow (1/4) :=
    phaseWindow_mono hs (hbase y hy)
  have hxball : x ∈ Metric.closedBall x (l*a) := Metric.mem_closedBall_self (by positivity)
  have hsp : phaseWindow s ⊆ positiveParameters := by
    intro y hy
    exact phaseWindow_positive (by linarith) hy
  let b := k+2*δ/(k*a)+2*C*l/k
  have hband : ∀ y ∈ Metric.closedBall x (l*a),
      ∀ v ∈ supportSet (onParameters P) positiveParameters y, |v 1-u| ≤ b := by
    intro y hy v hv
    have hzbound (z : ℝ) (hz : z ∈ ({0,k*a,-(k*a)} : Set ℝ)) : |z| ≤ k*a := by
      simp only [mem_insert_iff,mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simp; positivity
      · rw [abs_of_pos (mul_pos hk ha)]
      · rw [abs_neg,abs_of_pos (mul_pos hk ha)]
    have hhh := active_neighborhood_density_band ha hwβ0 (hsp (hbase y hy)) (mul_pos hk ha) hu
      (pressureSupport_iff.mpr hv)
      (fun z hz => happ _ (phaseWindow_mono hs (htest x hxball z (hzbound z hz))))
      (fun z hz => by
        have hp := hlip _ (phaseWindow_mono hs (htest y hy z (hzbound z hz)))
          _ (phaseWindow_mono hs (htest x hxball z (hzbound z hz)))
        rw [parameter_shift_dist] at hp
        exact hp.trans (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hy) hC))
    apply hhh.trans
    have hfirst : k*a/(2*w 0*a) ≤ k := by
      apply (div_le_iff₀ (by positivity : 0 < 2*w 0*a)).mpr
      have hm := mul_le_mul_of_nonneg_right (show 1 ≤ 2*w 0 by linarith [hwβ.1]) (mul_nonneg hk.le ha.le)
      nlinarith only [hm]
    have heq : 2*C*(l*a)/(k*a)=2*C*l/k := by field_simp
    rw [heq]
    dsimp [b]
    linarith
  obtain ⟨i,hi⟩ := common_group_of_density_band
    (fun y => supportSet (onParameters P) positiveParameters y)
    (Metric.closedBall x (l*a)) phaseSlope (fun v => v 1) ⟨x,hxball⟩
    (fun y hy => hgroups y (hbase y hy))
    (fun y hy => supportSet_nonempty isOpen_positiveParameters hP (hsp (hbase y hy)))
    hband (fun v w => by simpa only [PiLp.sub_apply,dist_eq_norm] using parameter_coord_abs_le (v-w) 1)
    phase_densities_separated hgap
  have he' : parameter e u ∈ supportSet (onParameters Q) positiveParameters x := by
    apply pressureSupport_iff.mp
    exact he
  have hnorm := support_transfer_bound (onParameters P) (onParameters Q) positiveParameters x (phaseSlope i)
    (parameter e u) (mul_pos hl ha) hr hδ (fun y hy => hsp (hbase y hy))
    (fun y hy => happ y (hbaseq y hy))
    (fun y hy => by
      obtain ⟨v,hv⟩ := supportSet_nonempty isOpen_positiveParameters hP (hsp (hbase y hy))
      exact ⟨v,hv,hi y hy hv⟩) he'
  have hsq : u^2 ≤ U^2 := (sq_le_sq₀ hub.1 hU).mpr hub.2
  refine ⟨i, Metric.mem_closedBall.mpr ?_⟩
  rw [dist_eq_norm]
  have heq : parameter (e+a*u^2/2) u-phaseSlope i =
      (parameter e u-phaseSlope i)+parameter (a*u^2/2) 0 := by
    ext j
    fin_cases j <;> simp
    ring
  rw [heq]
  have hnorm' := norm_add_le (parameter e u-phaseSlope i) (parameter (a*u^2/2) 0)
  rw [parameter_horizontal_norm,abs_of_nonneg (by positivity : 0 ≤ a*u^2/2)] at hnorm'
  nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQW_RadialTransition.MultiScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma multiscale_pressure_balls_oai {P Q : ℕ → Pressure} {a δ : ℕ → ℝ} {U C C₀ k l : ℝ}
    (ha : ∀ n, 0 < a n) (hδ : ∀ n, 0 ≤ δ n) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hk : 0 < k) (hl : 0 < l)
    (hP : ∀ n, ConvexOn ℝ positiveParameters (onParameters (P n)))
    (hQ : ∀ n, ConvexOn ℝ positiveParameters (onParameters (Q n)))
    (hnext : ∀ n, P (n+1)=idealAttraction (Q n) (a n))
    (happ : ∀ n x, x ∈ phaseWindow (1/4) → |onParameters (Q n) x-onParameters (P n) x| ≤ δ n)
    (hlip : ∀ n x, x ∈ phaseWindow (1/4) → ∀ y ∈ phaseWindow (1/4),
      |onParameters (P n) x-onParameters (P n) y| ≤ C*dist x y)
    (hinc : ∀ n x, x ∈ phaseWindow (1/4) → |onParameters (P (n+1)) x-onParameters (Q n) x| ≤ C₀*a n)
    (hact : ∀ n β h, 0 < β → ∃ u, ActiveShift (Q n) (a n) β h u)
    (hcut : ∀ n x, x ∈ phaseWindow (1/2) → ∃ u ∈ Icc (0:ℝ) U, ActiveShift (Q n) (a n) (x 0) (x 1) u)
    (hinit : ∀ x ∈ phaseWindow (1/4), HasPhaseGroups (P 0) x (phaseRadius/2) ∧
      |onParameters (P 0) x-onParameters threePlane x| ≤ pressureRadius/64)
    (hdom : ∀ n, (5/4*U+k+l+1)*(∑ j ∈ Finset.range n, a j) ≤ 1/8)
    (hrad : ∀ n, ∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2) ≤ phaseRadius/2)
    (hband : ∀ n, 2*(k+2*δ n/(k*a n)+2*C*l/k+phaseRadius)<packingDensity)
    (hpress : ∀ n, ∑ j ∈ Finset.range n, (δ j+C₀*a j) ≤ pressureRadius/64) :
    ∀ n, ∃ x ∈ Metric.ball phaseCenter (1/8),
      Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters (P n)) positiveParameters x := by
  let S := 5/4*U+k+l+1
  let s := fun n => 1/4-S*(∑ j ∈ Finset.range n, a j)
  let r := fun n => phaseRadius/2+∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs (n : ℕ) : 1/8 ≤ s n ∧ s n ≤ 1/4 := by
    have hn := hdom n
    have hm : 0 ≤ S*(∑ j ∈ Finset.range n, a j) :=
      mul_nonneg hS (Finset.sum_nonneg (fun j _ => (ha j).le))
    dsimp [s,S] at *
    constructor <;> linarith
  have hr (n : ℕ) : 0 ≤ r n ∧ r n ≤ phaseRadius := by
    have hnon : 0 ≤ ∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2) := by
      apply Finset.sum_nonneg
      intro j _
      have := ha j
      have := hδ j
      positivity
    have hb := hrad n
    dsimp [r]
    constructor <;> linarith [phaseRadius_pos]
  have hsr (n : ℕ) : s (n+1)=s n-S*a n := by
    dsimp [s]
    rw [Finset.sum_range_succ]
    ring
  have hrr (n : ℕ) : r (n+1)=r n+2*δ n/(l*a n)+a n*U^2/2 := by
    dsimp [r]
    rw [Finset.sum_range_succ]
    ring
  have hgroups : ∀ n x, x ∈ phaseWindow (s n) → HasPhaseGroups (P n) x (r n) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa [r] using (hinit x (by simpa [s] using hx)).1
    | succ n ih =>
      intro x hx
      rw [hnext n,hrr n]
      rw [hsr] at hx
      exact propagate_phase_groups (hP n) (hQ n) (ha n) (hδ n) hC hU hk hl (hr n).1 (hs n).2
        (by have := hband n; linarith [(hr n).2]) ih (happ n) (hlip n) (hact n) (hcut n) x hx
  have hclose : ∀ n x, x ∈ phaseWindow (1/4) →
      |onParameters (P n) x-onParameters threePlane x| ≤
        pressureRadius/64+∑ j ∈ Finset.range n, (δ j+C₀*a j) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa using (hinit x hx).2
    | succ n ih =>
      intro x hx
      have h1 := abs_sub_le (onParameters (P (n+1)) x) (onParameters (Q n) x) (onParameters (P n) x)
      have h2 := abs_sub_le (onParameters (P (n+1)) x) (onParameters (P n) x) (onParameters threePlane x)
      rw [Finset.sum_range_succ]
      linarith [hinc n x hx,happ n x hx,ih x hx]
  intro n
  apply pressure_ball_exists (hP n)
  · intro x hx
    have hh := hclose n x (phaseWindow_mono (by norm_num) hx)
    linarith [hpress n]
  · intro x hx
    exact ⟨r n,(hr n).2,hgroups n x (phaseWindow_mono (hs n).1 hx)⟩

end RadialTransition
end

end OAI
end

theorem solution : type_of% @OAI.RadialTransition.multiscale_pressure_balls_oai := @OAI.RadialTransition.multiscale_pressure_balls_oai
