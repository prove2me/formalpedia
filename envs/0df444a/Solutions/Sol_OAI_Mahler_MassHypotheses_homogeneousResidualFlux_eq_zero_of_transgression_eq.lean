-- Prove2me | solution 1 for OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:24:34.487347+00:00
-- url     : https://prove2.me/submissions/655e531a-d897-4fca-b5b8-16b05666d0d2

import Mathlib
import Definitions.Def_OAIQ2Ma000

section
-- module Solutions.OAIQ2_Mah.Mahler_CoordinateBall
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace MahlerStokes

lemma measurableSet_coordBall (n : ℕ) (R : ℝ) : MeasurableSet (coordBall n R) := by
  apply IsOpen.measurableSet
  exact isOpen_lt (by unfold radiusSq; fun_prop) continuous_const

lemma ball_slice {n : ℕ} (i : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) :
    {t : ℝ | i.insertNth t y ∈ coordBall (n+1) R} = Ioo (-chord R y) (chord R y) := by
  ext t
  simp only [coordBall, mem_ofPred_eq, radiusSq_insertNth, mem_Ioo, chord]
  by_cases h : 0 ≤ R ^ 2 - radiusSq y
  · rw [← abs_lt, ← Real.sqrt_sq_eq_abs t, Real.sqrt_lt_sqrt_iff (sq_nonneg t)]
    constructor <;> intro ht <;> linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    constructor
    · intro ht; nlinarith [sq_nonneg t]
    · intro ht; linarith

/-- Fubini in the i-th coordinate, for an actual restricted Lebesgue integral. -/
theorem setIntegral_slice {n : ℕ} (i : Fin (n+1)) {s : Set (Fin (n+1) → ℝ)}
    (hs : MeasurableSet s) (f : (Fin (n+1) → ℝ) → ℝ) (hf : IntegrableOn f s) :
    (∫ x in s, f x) = ∫ y : Fin n → ℝ, ∫ t in {t | i.insertNth t y ∈ s}, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => s.indicator f (i.insertNth p.1 p.2)) :=
    (hp.integrable_comp_emb e.symm.measurableEmbedding).2 (hf.integrable_indicator hs)
  calc
    (∫ x in s, f x) = ∫ p : ℝ × (Fin n → ℝ), s.indicator f (i.insertNth p.1 p.2) := by
      rw [← integral_indicator hs]
      exact (hp.integral_comp e.symm.measurableEmbedding (s.indicator f)).symm
    _ = ∫ y : Fin n → ℝ, ∫ t : ℝ, s.indicator f (i.insertNth t y) := (integral_prod _ hint).trans (integral_integral_swap hint)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      change _ = ∫ t in (fun t : ℝ => i.insertNth t y) ⁻¹' s, f (i.insertNth t y)
      rw [← integral_indicator (hs.preimage (by fun_prop : Measurable (fun t : ℝ => i.insertNth t y)))]
      congr 1

lemma hasDerivAt_insertNth {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (i.insertNth s y : Fin (n+1) → ℝ)) (Pi.single i 1) t := by
  have he : (fun s : ℝ => (i.insertNth s y : Fin (n+1) → ℝ)) =
      Function.update (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) i := by
    funext s
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp
    · intro j; simp
  rw [he]
  exact hasDerivAt_update _ i t

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_CoordinateAnnulus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Fundamental theorem of calculus on a punctured chord. No regularity
is required in the deleted middle interval. -/
theorem integral_punctured_chord {a A : ℝ} (ha : 0 ≤ a) (hA : a ≤ A)
    (f g : ℝ → ℝ)
    (hl : ∀ t ∈ Icc (-A) (-a), HasDerivAt f (g t) t)
    (hr : ∀ t ∈ Icc a A, HasDerivAt f (g t) t)
    (hgl : IntervalIntegrable g volume (-A) (-a))
    (hgr : IntervalIntegrable g volume a A) :
    (∫ t in Ioo (-A) A \ Ioo (-a) a, g t) =
      (f A - f (-A)) - (f a - f (-a)) := by
  have hs : Ioo (-A) A \ Ioo (-a) a = Ioc (-A) (-a) ∪ Ico a A := by
    ext t
    simp only [mem_sdiff, mem_Ioo, mem_union, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨⟨htl,htr⟩, ht⟩
      by_cases hta : t ≤ -a
      · exact Or.inl ⟨htl, hta⟩
      · exact Or.inr ⟨le_of_not_gt (fun h => ht ⟨lt_of_not_ge hta,h⟩), htr⟩
    · rintro (⟨htl,htr⟩ | ⟨htl,htr⟩)
      · exact ⟨⟨htl, by linarith⟩, fun h => by linarith [h.1]⟩
      · exact ⟨⟨by linarith, htr⟩, fun h => by linarith [h.2]⟩
  have hd : AEDisjoint volume (Ioc (-A) (-a)) (Ico a A) := by
    apply measure_mono_null (t := ({0} : Set ℝ))
    · intro t ht
      simp only [mem_inter_iff, mem_Ioc, mem_Ico, mem_singleton_iff] at ht ⊢
      linarith [ht.1.2, ht.2.1]
    · exact measure_singleton 0
  rw [hs, setIntegral_union₀ hd measurableSet_Ico.nullMeasurableSet
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (neg_le_neg hA)).1 hgl)
    ((intervalIntegrable_iff_integrableOn_Ico_of_le hA).1 hgr),
    integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_neg hA),
    ← intervalIntegral.integral_of_le hA]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (by simpa [uIcc_of_le (neg_le_neg hA)] using hl) hgl,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (by simpa [uIcc_of_le hA] using hr) hgr]
  ring

lemma chord_mono {n : ℕ} {a R : ℝ} (h : a^2 ≤ R^2) (y : Fin n → ℝ) :
    chord a y ≤ chord R y := Real.sqrt_le_sqrt (sub_le_sub_right h _)

lemma chord_shell {n : ℕ} {a R : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ coordBall n R) {t : ℝ}
    (ht : t ∈ Icc (-chord R y) (-chord a y) ∪ Icc (chord a y) (chord R y))
    (i : Fin (n+1)) : i.insertNth t y ∈ closedShell (n+1) a R := by
  have hR : (chord R y)^2 = R^2 - radiusSq y :=
    Real.sq_sqrt (by change radiusSq y < R^2 at hy; linarith)
  have ha : a^2 - radiusSq y ≤ (chord a y)^2 := by
    by_cases h : 0 ≤ a^2 - radiusSq y
    · exact (Real.sq_sqrt h).ge
    · exact le_trans (le_of_not_ge h) (sq_nonneg _)
  have hnA : 0 ≤ chord R y := Real.sqrt_nonneg _
  have hna : 0 ≤ chord a y := Real.sqrt_nonneg _
  have htabs : chord a y ≤ |t| ∧ |t| ≤ chord R y := by
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith [ht.2])]
      constructor <;> linarith [ht.1, ht.2]
    · rw [abs_of_nonneg (by linarith [ht.1])]
      exact ht
  have hlo := (sq_le_sq₀ hna (abs_nonneg t)).2 htabs.1
  have hhi := (sq_le_sq₀ (abs_nonneg t) hnA).2 htabs.2
  change a^2 ≤ radiusSq (i.insertNth t y) ∧ radiusSq (i.insertNth t y) ≤ R^2
  rw [radiusSq_insertNth]
  rw [sq_abs] at hlo hhi
  constructor <;> linarith

lemma boundary_difference_zero {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) {y : Fin n → ℝ} (hy : y ∉ coordBall n R) :
    f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y) = 0 := by
  have hz : chord R y = 0 := Real.sqrt_eq_zero_of_nonpos
    (by change ¬ radiusSq y < R^2 at hy; linarith)
  simp [hz]

lemma integral_boundary_difference {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) :
    (∫ y : Fin n → ℝ, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) =
      ∫ y in coordBall n R, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y) := by
  rw [← integral_indicator (measurableSet_coordBall n R)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ coordBall n R
  · simp [hy]
  · simp [hy, boundary_difference_zero i R f hy]

/-- Divergence for one component on an annulus. Differentiability and
continuity of the actual partial derivative are required only on its closed
shell, so a singularity anywhere inside the hole is permitted. -/
theorem integral_partial_coordAnnulus {n : ℕ} (i : Fin (n+1)) {a R : ℝ}
    (haR : a^2 ≤ R^2) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ f x)
    (hg : ContinuousOn (fun x => fderiv ℝ f x (Pi.single i 1)) (closedShell (n+1) a R))
    (hgi : IntegrableOn (fun x => fderiv ℝ f x (Pi.single i 1)) (coordAnnulus (n+1) a R))
    (hbR : Integrable (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)))
    (hba : Integrable (fun y : Fin n → ℝ =>
      f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y))) :
    (∫ x in coordAnnulus (n+1) a R, fderiv ℝ f x (Pi.single i 1)) =
      (∫ y in coordBall n R, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) -
      ∫ y in coordBall n a, f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y) := by
  rw [setIntegral_slice i (s := coordAnnulus (n+1) a R) ((measurableSet_coordBall _ _).diff (measurableSet_coordBall _ _)) _ hgi]
  have hslice (y : Fin n → ℝ) :
      {t : ℝ | i.insertNth t y ∈ coordAnnulus (n+1) a R} =
        Ioo (-chord R y) (chord R y) \ Ioo (-chord a y) (chord a y) := by
    change {t | i.insertNth t y ∈ coordBall (n+1) R} \ {t | i.insertNth t y ∈ coordBall (n+1) a} = _
    rw [ball_slice, ball_slice]
  simp_rw [hslice]
  have he (y : Fin n → ℝ) :
      (∫ t in Ioo (-chord R y) (chord R y) \ Ioo (-chord a y) (chord a y),
        fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) =
      (f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) -
      (f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y)) := by
    by_cases hy : y ∈ coordBall n R
    · have hleft : MapsTo (fun t : ℝ => i.insertNth t y) (Icc (-chord R y) (-chord a y))
          (closedShell (n+1) a R) := fun t ht => chord_shell hy (Or.inl ht) i
      have hright : MapsTo (fun t : ℝ => i.insertNth t y) (Icc (chord a y) (chord R y))
          (closedShell (n+1) a R) := fun t ht => chord_shell hy (Or.inr ht) i
      apply integral_punctured_chord (a := chord a y) (A := chord R y) (Real.sqrt_nonneg _) (chord_mono haR y)
        (fun t => f (i.insertNth t y)) (fun t => fderiv ℝ f (i.insertNth t y) (Pi.single i 1))
      · intro t ht
        exact (hf _ (hleft ht)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i y t)
      · intro t ht
        exact (hf _ (hright ht)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i y t)
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (neg_le_neg (chord_mono haR y))]
        exact hg.comp (by fun_prop) hleft
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (chord_mono haR y)]
        exact hg.comp (by fun_prop) hright
    · have hya : y ∉ coordBall n a := by
        intro h; apply hy; change radiusSq y < R^2; exact lt_of_lt_of_le h haR
      have hz : chord R y = 0 := Real.sqrt_eq_zero_of_nonpos
        (by change ¬radiusSq y < R^2 at hy; linarith)
      simp [hz, boundary_difference_zero i a f hya]
  simp_rw [he]
  rw [integral_sub hbR hba, integral_boundary_difference i R f, integral_boundary_difference i a f]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ShellRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma continuous_radiusSq (n : ℕ) : Continuous (radiusSq (n := n)) := by
  unfold radiusSq; fun_prop

lemma isCompact_coordClosedBall (n : ℕ) (R : ℝ) : IsCompact (coordClosedBall n R) := by
  have hs : coordClosedBall n R ⊆ Icc (fun _ => -|R|) (fun _ => |R|) := by
    intro x hx
    have hi (i : Fin n) : |x i| ≤ |R| := by
      have hsum : x i ^ 2 ≤ radiusSq x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have hx' : radiusSq x ≤ R^2 := hx
      nlinarith [sq_abs (x i), sq_abs R, abs_nonneg (x i), abs_nonneg R]
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_le (continuous_radiusSq n) continuous_const) hs

lemma isCompact_closedShell (n : ℕ) (a R : ℝ) : IsCompact (closedShell n a R) := by
  apply (isCompact_coordClosedBall n R).of_isClosed_subset
  · exact (isClosed_le continuous_const (continuous_radiusSq n)).inter
      (isClosed_le (continuous_radiusSq n) continuous_const)
  · intro x hx; exact hx.2

lemma coordAnnulus_subset_shell (n : ℕ) (a R : ℝ) :
    coordAnnulus n a R ⊆ closedShell n a R := by
  intro x hx
  exact ⟨le_of_not_gt hx.2, hx.1.le⟩

lemma integrableOn_shell_annulus {n : ℕ} {a R : ℝ} {g : (Fin n → ℝ) → ℝ}
    (hg : ContinuousOn g (closedShell n a R)) : IntegrableOn g (coordAnnulus n a R) :=
  (hg.integrableOn_compact (isCompact_closedShell n a R)).mono_set (coordAnnulus_subset_shell n a R)

lemma radiusSq_boundary {n : ℕ} (i : Fin (n+1)) (R : ℝ) {y : Fin n → ℝ}
    (hy : y ∈ coordClosedBall n R) :
    radiusSq (i.insertNth (chord R y) y) = R^2 ∧
    radiusSq (i.insertNth (-chord R y) y) = R^2 := by
  have hc : (chord R y)^2 = R^2 - radiusSq y := Real.sq_sqrt (sub_nonneg.mpr hy)
  simp only [radiusSq_insertNth, neg_sq]
  constructor <;> linarith

/-- Boundary integrability follows from ordinary continuity on the sphere. -/
lemma integrable_boundary_difference {n : ℕ} (i : Fin (n+1)) (R : ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContinuousOn f {x | radiusSq x = R^2}) :
    Integrable (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) := by
  have hch : Continuous (chord (n := n) R) := by
    unfold chord; exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_radiusSq n))
  have htop : ContinuousOn (fun y : Fin n → ℝ => f (i.insertNth (chord R y) y)) (coordClosedBall n R) :=
    hf.comp (by fun_prop) (fun y hy => (radiusSq_boundary i R hy).1)
  have hbot : ContinuousOn (fun y : Fin n → ℝ => f (i.insertNth (-chord R y) y)) (coordClosedBall n R) :=
    hf.comp (by fun_prop) (fun y hy => (radiusSq_boundary i R hy).2)
  have hint : IntegrableOn (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) (coordBall n R) :=
    ((htop.sub hbot).integrableOn_compact (isCompact_coordClosedBall n R)).mono_set (fun x hy => (show radiusSq x < R^2 from hy).le)
  have he : (coordBall n R).indicator (fun y : Fin n → ℝ =>
      f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) =
      (fun y : Fin n → ℝ => f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) := by
    funext y
    by_cases hy : y ∈ coordBall n R
    · simp [hy]
    · simp [hy, boundary_difference_zero i R f hy]
  rw [← he]
  exact hint.integrable_indicator (measurableSet_coordBall n R)

/-- The annulus identity under local C1 assumptions only; integrability of
both volume and boundary terms is proved, not assumed. -/
theorem integral_partial_annulus_of_C1 {n : ℕ} (i : Fin (n+1)) {a R : ℝ}
    (haR : a^2 ≤ R^2) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ f x)
    (hg : ContinuousOn (fun x => fderiv ℝ f x (Pi.single i 1)) (closedShell (n+1) a R)) :
    (∫ x in coordAnnulus (n+1) a R, fderiv ℝ f x (Pi.single i 1)) =
      (∫ y in coordBall n R, f (i.insertNth (chord R y) y) - f (i.insertNth (-chord R y) y)) -
      ∫ y in coordBall n a, f (i.insertNth (chord a y) y) - f (i.insertNth (-chord a y) y) := by
  have hc : ContinuousOn f (closedShell (n+1) a R) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  apply integral_partial_coordAnnulus i haR f hf hg (integrableOn_shell_annulus hg)
  · apply integrable_boundary_difference
    exact hc.mono (fun x hx => ⟨hx ▸ haR, hx.le⟩)
  · apply integrable_boundary_difference
    exact hc.mono (fun x hx => ⟨hx.ge, hx ▸ haR⟩)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FormStokes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Punctured-ball Stokes for actual differential forms, with no regularity
assumption in the interior of the removed inner ball. -/
theorem integral_extDeriv_coordAnnulus {n : ℕ} {a R : ℝ} (haR : a^2 ≤ R^2)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ ω x)
    (hD : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i))
      (closedShell (n+1) a R)) :
    (∫ x in coordAnnulus (n+1) a R, extDeriv ω x (coordinateBasis (n+1))) =
      (∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n R,
          ω (i.insertNth (chord R y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord R y) y) (i.removeNth (coordinateBasis (n+1)))) -
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n a,
          ω (i.insertNth (chord a y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord a y) y) (i.removeNth (coordinateBasis (n+1))) := by
  have he : (∫ x in coordAnnulus (n+1) a R, extDeriv ω x (coordinateBasis (n+1))) =
      ∫ x in coordAnnulus (n+1) a R, ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i) := by
    apply setIntegral_congr_fun ((measurableSet_coordBall _ _).diff (measurableSet_coordBall _ _))
    intro x hx
    simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
      extDeriv_apply (hω x (coordAnnulus_subset_shell _ _ _ hx)) (coordinateBasis (n+1))
  rw [he, integral_finsetSum _ (fun i _ => (integrableOn_shell_annulus (hD i)).const_mul _),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [coordinateBasis] at *
  rw [integral_const_mul, integral_partial_annulus_of_C1 i haR _
    (fun x hx => (hω x hx).continuousAlternatingMap_apply_const _) (hD i), mul_sub]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PuncturedBallStokes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma radiusSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ radiusSq x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

lemma coordBall_zero (n : ℕ) : coordBall n 0 = ∅ := by
  ext x
  simp only [coordBall, mem_ofPred_eq, zero_pow (by decide : 2 ≠ 0), mem_empty_iff_false, iff_false]
  exact not_lt_of_ge (radiusSq_nonneg x)

lemma closedShell_zero (n : ℕ) (R : ℝ) : closedShell n 0 R = coordClosedBall n R := by
  ext x
  simp [closedShell, coordClosedBall, radiusSq_nonneg]

/-- Ball Stokes needs C1 regularity only near the closed ball, not globally. -/
theorem integral_extDeriv_ball_of_C1 {n : ℕ} (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ∀ x ∈ coordClosedBall (n+1) R, DifferentiableAt ℝ ω x)
    (hD : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i)) (coordClosedBall (n+1) R)) :
    (∫ x in coordBall (n+1) R, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n R,
          ω (i.insertNth (chord R y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord R y) y) (i.removeNth (coordinateBasis (n+1))) := by
  have hw : ∀ x ∈ closedShell (n+1) 0 R, DifferentiableAt ℝ ω x := by
    simpa only [closedShell_zero] using hω
  have hd : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i))
      (closedShell (n+1) 0 R) := by
    simpa only [closedShell_zero] using hD
  simpa [coordAnnulus, coordBall_zero] using
    integral_extDeriv_coordAnnulus (a := 0) (R := R) (by simpa using sq_nonneg R) ω hw hd

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PunctureCutoff
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem sphereFlux_congr {n : ℕ} (r : ℝ)
    (ω η : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (he : ∀ x, radiusSq x = r^2 → ω x = η x) : sphereFlux r ω = sphereFlux r η := by
  unfold sphereFlux
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply setIntegral_congr_fun (measurableSet_coordBall n r)
  intro y hy
  obtain ⟨hp, hm⟩ := radiusSq_boundary i r (show y ∈ coordClosedBall n r from (show radiusSq y < r^2 from hy).le)
  dsimp only
  rw [he _ hp, he _ hm]

 theorem integral_extDeriv_ball_local {n : ℕ} {U : Set (Fin (n+1) → ℝ)} (r : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (hBU : coordClosedBall (n+1) r ⊆ U) :
    (∫ x in coordBall (n+1) r, extDeriv ω x (coordinateBasis (n+1))) = sphereFlux r ω := by
  apply integral_extDeriv_ball_of_C1 r ω
  · intro x hx
    exact (hω.contDiffAt (hU.mem_nhds (hBU hx))).differentiableAt one_ne_zero
  · intro i x hx
    have hcoeff : ContDiffOn ℝ 1 (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) U :=
      (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (coordinateBasis (n+1)))).contDiff.comp_contDiffOn hω
    exact (((hcoeff.contDiffAt (hU.mem_nhds (hBU hx))).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).continuousWithinAt

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ClosedBoundaryStokes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- C2 regularity of a form gives C1 regularity of its actual exterior derivative. -/
theorem contDiffAt_extDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} {x : E}
    (hω : ContDiffAt ℝ 2 ω x) : ContDiffAt ℝ 1 (extDeriv ω) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ ω) x := hω.fderiv_right (by norm_num)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ (n := n)).contDiff.contDiffAt.comp x hd

/-- Smooth separation extends a C2 form near a closed subset of its open
regularity domain, with exact equality on a neighborhood of that subset. -/
theorem exists_closed_set_form_extension {d n : ℕ} {U K : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 2 ω U) :
    ∃ η : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ,
      ContDiff ℝ 2 η ∧ (∀ x ∈ K, η =ᶠ[𝓝 x] ω) := by
  have hdis : Disjoint Uᶜ K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    exact hx (hKU hxK)
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin d → ℝ) hU.isClosed_compl hK hdis (n := 2)
  have hχ : ContDiff ℝ 2 χ := χ.contMDiff.contDiff
  refine ⟨fun x => χ x • ω x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hω.contDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in 𝓝 x, χ y = 0 := hχ0.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const (c := (0 : (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    have ho : ∀ᶠ y in 𝓝 x, χ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [ho] with y hy
    simp [hy]

/-- An exact form integrates to zero over the closed sphere. Its primitive
need only be C2 on an open neighborhood of the sphere, not inside the ball. -/
theorem sphereFlux_extDeriv_eq_zero {n : ℕ} {U : Set (Fin (n+1+1) → ℝ)}
    (r : ℝ) (hU : IsOpen U)
    (hSU : {x | radiusSq x = r^2} ⊆ U)
    (ω : (Fin (n+1+1) → ℝ) → (Fin (n+1+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 2 ω U) : sphereFlux r (extDeriv ω) = 0 := by
  obtain ⟨η, hη, he⟩ := exists_closed_set_form_extension hU
    (isClosed_eq (continuous_radiusSq _) continuous_const) hSU ω hω
  have hde (x) (hx : radiusSq x = r^2) : extDeriv η x = extDeriv ω x := by
    unfold extDeriv
    rw [(he x hx).fderiv_eq]
  rw [← sphereFlux_congr r (extDeriv η) (extDeriv ω) hde]
  have hs := integral_extDeriv_ball_local r (extDeriv η) isOpen_univ
    (contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_extDeriv hη.contDiffAt)).contDiffOn
    (subset_univ _)
  rw [← hs]
  have hd : extDeriv (extDeriv η) = 0 := extDeriv_extDeriv hη (by simp)
  simp [hd]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_WedgeAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedge_compLinearMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).compLinearMap L = wedge (a.compLinearMap L) (b.compLinearMap L) := by
  ext v
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod b (fun i => L (v i))) =
    (LinearMap.mul' ℝ ℂ) ((a.compLinearMap L).domCoprod (b.compLinearMap L) v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply]

lemma wedgePower_compLinearMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    (wedgePower a k).compLinearMap L = wedgePower (a.compLinearMap L) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (wedge a (wedgePower a k)).compLinearMap L = _
    rw [wedge_compLinearMap, ih]
    rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_CovectorVolume
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct BigOperators

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Exterior multiplication of simple forms concatenates their covectors,
with the exact shuffle normalization and slot order. -/
theorem wedge_covectorVolume (l : ι → T →ₗ[ℝ] ℂ) (r : κ → T →ₗ[ℝ] ℂ) :
    wedge (covectorVolume l) (covectorVolume r) = covectorVolume (Sum.elim l r) := by
  unfold covectorVolume wedge
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization]
  congr 1
  ext v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    LinearMap.mul'_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

lemma wedge_sum_left {J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : T [⋀^κ]→ₗ[ℝ] ℂ) : wedge (∑ j ∈ s, a j) b = ∑ j ∈ s, wedge (a j) b := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.sum_tmul, map_sum]

lemma wedge_sum_right {J : Type*} (s : Finset J) (a : T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : J → T [⋀^κ]→ₗ[ℝ] ℂ) : wedge a (∑ j ∈ s, b j) = ∑ j ∈ s, wedge a (b j) := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.tmul_sum, map_sum]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric
open scoped Pointwise
namespace MahlerStokes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma sphereIsometry_cone_preimage (e : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereIsometry e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, e z, ⟨sphereIsometry e z, hz, rfl⟩, (e.map_smul r z).symm⟩
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, he⟩
    refine ⟨r, hr, e.symm z, ⟨(sphereIsometry e).symm z, ?_, rfl⟩, ?_⟩
    · simpa using hz
    · apply e.injective
      simpa using he

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Surface area induced by ambient volume is transported without a factor
by a volume-preserving real linear isometry. -/
theorem measurePreserving_sphereIsometry (e : E ≃ₗᵢ[ℝ] F)
    (μ : Measure E) (ν : Measure F) (he : MeasurePreserving e μ ν) :
    MeasurePreserving (sphereIsometry e) μ.toSphere ν.toSphere := by
  refine ⟨(sphereIsometry e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereIsometry e).measurable hs,
    Measure.toSphere_apply' _ ((sphereIsometry e).measurable hs),
    Measure.toSphere_apply' _ hs, sphereIsometry_cone_preimage]
  rw [e.toLinearEquiv.finrank_eq]
  congr 1
  exact he.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExteriorPower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

lemma pairedCovectors_succ {k : ℕ} (p : Fin (k+1) → Fin 2 → T →ₗ[ℝ] ℂ) :
    pairedCovectors p = Sum.elim (p 0) (pairedCovectors (fun i => p i.succ)) := by
  funext s
  cases s <;> rfl

/-- Expand the actual shuffle power as a sum of determinants of selected
covector pairs. This identity includes every term, also repeated selections. -/
theorem wedgePower_sum_pairs {J : Type*} [Fintype J]
    (p : J → Fin 2 → T →ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (∑ j, covectorVolume (p j)) k =
      ∑ q : Fin k → J, covectorVolume (pairedCovectors (fun i => p (q i))) := by
  classical
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = (∑ q : Fin 0 → J, covectorVolume
      (pairedCovectors (fun index => p (q index)))) v
    simp only [Fintype.sum_unique]
    rw [covectorVolume_apply]
    let : IsEmpty (WedgePowerSlots 0) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty.symm
  | succ k ih =>
    change wedge (∑ j, covectorVolume (p j)) (wedgePower (∑ j, covectorVolume (p j)) k) = _
    rw [ih, wedge_sum_left]
    simp_rw [wedge_sum_right, wedge_covectorVolume]
    simp_rw [pairedCovectors_succ]
    trans ∑ q : J × (Fin k → J), covectorVolume (Sum.elim (p q.1) (pairedCovectors (fun i => p (q.2 i))))
    · exact (Fintype.sum_prod_type (fun q : J × (Fin k → J) => covectorVolume (Sum.elim (p q.1) (pairedCovectors (fun i => p (q.2 i)))))).symm
    · apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => J))
      intro q
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [show wedgePowerSlotsDecidableEq (k+1) =
        (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
      rfl

lemma pairPermutation_sign {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (pairPermutation σ) = 1 := by
  simp [pairPermutation, Equiv.Perm.sign_prodCongrLeft]

lemma pairedCovectors_perm {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (Fin k)) :
    pairedCovectors (fun i => p (σ i)) = pairedCovectors p ∘ pairPermutation σ := by
  funext s
  simp [pairedCovectors, pairPermutation, Equiv.prodCongrLeft]

lemma covectorVolume_pairs_perm {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (Fin k)) :
    covectorVolume (pairedCovectors (fun i => p (σ i))) = covectorVolume (pairedCovectors p) := by
  ext v
  rw [pairedCovectors_perm, covectorVolume_apply, covectorVolume_apply]
  change Matrix.det ((Matrix.of (fun row column => pairedCovectors p column (v row))).submatrix
    id (pairPermutation σ)) = _
  rw [Matrix.det_permute', pairPermutation_sign]
  simp only [Units.val_one, Int.cast_one, one_mul]

lemma covectorVolume_pairs_noninjective {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (q : Fin k → Fin k) (hq : ¬Function.Injective q) :
    covectorVolume (pairedCovectors (fun i => p (q i))) = 0 := by
  classical
  obtain ⟨i,j,hij,hne⟩ : ∃ i j, q i = q j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using hq
  ext v
  rw [covectorVolume_apply]
  apply Matrix.det_zero_of_column_eq
    (i := (pairSlotEquiv k).symm (i,0)) (j := (pairSlotEquiv k).symm (j,0))
  · intro h
    have h' := congrArg (fun s => (pairSlotEquiv k s).1) h
    exact hne (by simpa using h')
  · intro s
    simp [pairedCovectors, hij]

/-- The n-fold shuffle power of n simple two-forms is n! times their
interleaved covector volume. Repeated choices vanish; pair permutations have
positive sign. This yields the factorial in the normalization. -/
theorem wedgePower_sum_pairs_top (k : ℕ) (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ) :
    wedgePower (∑ j, covectorVolume (p j)) k =
      (k.factorial : ℂ) • covectorVolume (pairedCovectors p) := by
  classical
  rw [wedgePower_sum_pairs]
  calc
    (∑ q : Fin k → Fin k, covectorVolume (pairedCovectors (fun i => p (q i)))) =
        ∑ q : Fin k → Fin k with Function.Bijective q,
          covectorVolume (pairedCovectors (fun i => p (q i))) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun q _ hq => ?_)).symm
      apply covectorVolume_pairs_noninjective p q
      intro hi
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, Finite.surjective_of_injective hi⟩)
    _ = ∑ σ : Equiv.Perm (Fin k), covectorVolume (pairedCovectors (fun i => p (σ i))) :=
      Finset.sum_bij (fun q h => Equiv.ofBijective q (Finset.mem_filter.1 h).2)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => by injection h)
        (fun b _ => ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, b.bijective⟩,
          Equiv.coe_fn_injective rfl⟩) (fun _ _ => rfl)
    _ = (k.factorial : ℂ) • covectorVolume (pairedCovectors p) := by
      simp only [covectorVolume_pairs_perm, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      exact (Nat.cast_smul_eq_nsmul ℂ k.factorial _).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HolomorphicRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric Filter MeasureTheory
open scoped Topology Interval

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex Schwarz estimate gives a local bound on the full derivative,
from first-order holomorphicity alone. -/
lemma locally_bounded_fderiv {f : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    ∃ r > 0, ∃ C ≥ 0, ball x r ⊆ U ∧
      ∀ y ∈ ball x r, ‖fderiv ℂ f y‖ ≤ C := by
  have hc := (hf x hx).differentiableAt (hU.mem_nhds hx) |>.continuousAt
  have hn : U ∩ f ⁻¹' ball (f x) 1 ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (hc.preimage_mem_nhds (ball_mem_nhds _ zero_lt_one))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, 2 / (r / 2), by positivity, ?_, ?_⟩
  · intro y hy
    exact (hsub (ball_subset_ball (by linarith) hy)).1
  · intro y hy
    have hball : ball y (r / 2) ⊆ ball x r := by
      intro z hz
      have := dist_triangle z y x
      rw [mem_ball] at hy hz ⊢
      linarith
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      (hf.mono (hball.trans (fun z hz => (hsub hz).1))) ?_ (by positivity)
    intro z hz
    have hzy := (hsub (hball hz)).2
    have hyx := (hsub (ball_subset_ball (by linarith) hy)).2
    rw [mem_closedBall]
    have := dist_triangle (f z) (f x) (f y)
    change dist (f z) (f x) < 1 at hzy
    change dist (f y) (f x) < 1 at hyx
    rw [dist_comm (f x) (f y)] at this
    linarith

variable [FiniteDimensional ℂ E]

/-- Differentiability of a Cauchy integral in an ambient finite-dimensional
complex parameter. The derivative bound is obtained locally by Schwarz. -/
lemma differentiable_cauchy_parameter {f : E → ℂ} {U : Set E} {x v : E}
    {R C r : ℝ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : 0 < R) (hr : 0 < r) (hv : r * ‖v‖ < R / 2)
    (hsub : ball x R ⊆ U)
    (hb : ∀ y ∈ ball x R, ‖fderiv ℂ f y‖ ≤ C) :
    DifferentiableAt ℂ
      (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) x := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let c : ℝ → ℂ := circleMap 0 r
  let k : ℝ → ℂ := fun t => (c t * I) * (1 / c t ^ 2)
  have hc : Continuous c := continuous_circleMap _ _
  have hcn (t : ℝ) : ‖c t‖ = r := by simp [c, abs_of_pos hr]
  have hcz (t : ℝ) : c t ≠ 0 := by
    intro h
    have := hcn t
    rw [h, norm_zero] at this
    linarith
  have hk : Continuous k := (hc.mul continuous_const).mul
    (continuous_const.div (hc.pow 2) (fun t => pow_ne_zero _ (hcz t)))
  have hkn (t : ℝ) : ‖k t‖ = 1 / r := by
    simp [k, norm_pow, hcn, norm_I]
    field_simp
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      y + c t • v ∈ ball x R := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have htri := norm_add_le (y - x) (c t • v)
    have he : y + c t • v - x = (y - x) + c t • v := by abel
    rw [he]
    rw [norm_smul, hcn] at htri
    linarith
  have hcont {y : E} (hy : y ∈ ball x (R / 2)) :
      Continuous (fun t => k t * f (y + c t • v)) := by
    apply hk.mul
    exact hf.continuousOn.comp_continuous (by fun_prop) (fun t => hsub (hshift hy t))
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t => k t • fderiv ℂ f (y + c t • v)
  have hd {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      HasFDerivAt (fun y => k t * f (y + c t • v)) (F' y t) y := by
    have hf' := ((hf _ (hsub (hshift hy t))).differentiableAt
      (hU.mem_nhds (hsub (hshift hy t)))).hasFDerivAt
    simpa only [F', Function.comp_apply, id_eq, ContinuousLinearMap.comp_id] using
      (hf'.comp y ((hasFDerivAt_id y).add_const (c t • v))).const_mul (k t)
  have hm : AEStronglyMeasurable (F' x) := by
    apply Measurable.aestronglyMeasurable
    exact hk.measurable.smul ((measurable_fderiv ℂ f).comp
      (show Continuous (fun t => x + c t • v) by fun_prop).measurable)
  have hint := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := fun y t => k t * f (y + c t • v)) (F' := F')
    (bound := fun _ => (1 / r) * C) (ball_mem_nhds x (by positivity : 0 < R / 2))
    (by filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
        exact (hcont hy).aestronglyMeasurable)
    ((hcont (mem_ball_self (by positivity))).intervalIntegrable _ _)
    hm.restrict
    (by filter_upwards [] with t ht y hy
        simp only [F', norm_smul, hkn]
        exact mul_le_mul_of_nonneg_left (hb _ (hshift hy t)) (by positivity))
    (intervalIntegrable_const)
    (by filter_upwards [] with t ht y hy; exact hd hy t)
  have he : (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) =
      (fun y => ∫ t in (0 : ℝ)..2 * Real.pi, k t * f (y + c t • v)) := by
    funext y
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul, c, k, mul_assoc]
  rw [he]
  exact hint.differentiableAt

/-- A directional component of the ambient first derivative is holomorphic.
Only first-order holomorphicity on the open domain is assumed. -/
theorem differentiableAt_fderiv_apply_of_open {f : E → ℂ} {U : Set E} {x v : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  obtain ⟨R, hR, C, hC, hsub, hb⟩ := locally_bounded_fderiv hU hx hf
  let r := (R / 2) / (‖v‖ + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : r * ‖v‖ < R / 2 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < ‖v‖ + 1)]
    nlinarith
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) {z : ℂ}
      (hz : z ∈ closedBall 0 r) : y + z • v ∈ U := by
    apply hsub
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hzn : ‖z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have htri := norm_add_le (y - x) (z • v)
    have he : y + z • v - x = (y - x) + z • v := by abel
    rw [he]
    rw [norm_smul] at htri
    have hmul := mul_le_mul_of_nonneg_right hzn (norm_nonneg v)
    linarith
  have he : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) := by
    filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
    have hl : Differentiable ℂ (fun z : ℂ => y + z • v) := by fun_prop
    have hline : DifferentiableOn ℂ (fun z : ℂ => f (y + z • v)) (closedBall 0 r) :=
      hf.comp hl.differentiableOn (fun z hz => hshift hy hz)
    have hcauchy := hline.deriv_eq_smul_circleIntegral hr
    have hfy : DifferentiableAt ℂ f y :=
      (hf y (by simpa using hshift hy (mem_closedBall_self hr.le))).differentiableAt
        (hU.mem_nhds (by simpa using hshift hy (mem_closedBall_self hr.le)))
    have hl' : HasDerivAt (fun z : ℂ => y + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have hfy' : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using hfy.hasFDerivAt
    have hder := hfy'.comp_hasDerivAt 0 hl'
    change HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f y v) 0 at hder
    rw [hder.deriv] at hcauchy
    simp only [sub_zero, smul_eq_mul] at hcauchy ⊢
    rw [hcauchy, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  exact ((differentiable_cauchy_parameter hU hf hR hr hv hsub hb).const_mul
    (2 * Real.pi * I : ℂ)⁻¹).congr_of_eventuallyEq he

/-- Holomorphic functions on open finite-dimensional complex domains are C^k
for every finite k. Smoothness is derived, not added to the hypotheses. -/
theorem contDiffOn_nat_of_differentiableOn_open {U : Set E} (hU : IsOpen U)
    (k : ℕ) {f : E → ℂ} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ k f U := by
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiffOn_succ_of_fderiv_apply hf (by simp)
    intro v
    have hd : DifferentiableOn ℂ (fun y => fderiv ℂ f y v) U :=
      fun y hy => (differentiableAt_fderiv_apply_of_open hU hy hf).differentiableWithinAt
    apply (ih hd).congr
    intro y hy
    rw [fderivWithin_of_isOpen hU hy]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Hessian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

namespace Mahler
variable {E : Type*} [normedAddCommGroupE : NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

variable {ι : Type*} [Fintype ι]

omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma tau_nonneg [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : 0 ≤ tau f x :=
  Finset.sum_nonneg (fun j _ => normSq_nonneg (f j x))
omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma energy_eq_tau [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : energy f x = (tau f x : ℂ) := by
  simp [energy, tau, Complex.normSq_eq_conj_mul_self]
lemma logTau_eq (f : ι → E → ℂ) : logTau f = fun x => Complex.log (energy f x) := by
  funext x
  rw [logTau, energy_eq_tau, Complex.ofReal_log (tau_nonneg f x)]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExteriorFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma differentiableAt_oneForm [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) : DifferentiableAt ℝ (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x ha

/-- Exterior differentiation uses the usual unnormalized alternating sum. -/
lemma extDeriv_oneForm {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    extDeriv (oneForm a) x ![v, w] =
      fderiv ℝ (fun y => a y w) x v - fderiv ℝ (fun y => a y v) x w := by
  rw [extDeriv_apply (differentiableAt_oneForm ha)]
  simp [Fin.sum_univ_two, Fin.removeNth, oneForm_apply, sub_eq_add_neg]

lemma differentiableAt_dcLinear {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact ((hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)).differentiableAt (by norm_num)

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

namespace Mahler

lemma polynomialMap_differentiable {n N : ℕ} (G : Fin N → MvPolynomial (Fin n) ℂ) :
    ∀ j, Differentiable ℂ (polynomialMap G j) := by
  intro j x
  have ha : AnalyticAt ℂ (fun z : ComplexEuclidean n =>
      MvPolynomial.eval (fun i => z i) (G j)) x :=
    AnalyticAt.aeval_mvPolynomial
      (fun i : Fin n => (EuclideanSpace.proj (𝕜 := ℂ) i).analyticAt x) (G j)
  exact ha.differentiableAt

lemma tau_pos_of_component_ne_zero {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ι → E → ℂ} {x : E} (hf : ∃ j, f j x ≠ 0) : 0 < tau f x := by
  obtain ⟨j, hj⟩ := hf
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
  exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (f k x)) (Finset.mem_univ j)

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereForms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma coordinateMap_differentiable (n : ℕ) : ∀ j, Differentiable ℂ (coordinateMap n j) :=
  fun j => (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable

lemma coordinateMap_tau_pos {n : ℕ} {z : ComplexEuclidean n} (hz : z ≠ 0) :
    0 < tau (coordinateMap n) z := by
  apply tau_pos_of_component_ne_zero
  by_contra h
  push Not at h
  apply hz
  ext i
  exact h i

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_NormSquareForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma normEnergy_contDiff (n : ℕ) : ContDiff ℝ 2 (normEnergy n) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_id.norm_sq (𝕜 := ℝ))

/-- The actual d^c of the Euclidean squared norm. -/
lemma dc_normEnergy {n : ℕ} (x v : ComplexEuclidean n) :
    dc (normEnergy n) x v = (-1 / 2 : ℂ) * (inner ℝ x (I • v) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (normEnergy n) _ x at hd
  rw [dc, hd.fderiv]
  simp
  ring

lemma real_inner_complexStructure_swap {n : ℕ} (v w : ComplexEuclidean n) :
    inner ℝ w (I • v) = -inner ℝ v (I • w) := by
  simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

/-- The exterior normalization dd^c |z|^2 is the
standard symplectic two-form, with positive dx_k wedge dy_k orientation. -/
theorem extDeriv_dc_normEnergy {n : ℕ} (x v w : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v, w] =
      ((∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re) : ℝ) : ℂ) := by
  rw [extDeriv_oneForm (differentiableAt_dcLinear (normEnergy_contDiff n).contDiffAt)]
  have hd (a b : ComplexEuclidean n) :
      fderiv ℝ (fun y => dcLinear (normEnergy n) y a) x b =
        (-1 / 2 : ℂ) * (inner ℝ b (I • a) : ℂ) := by
    have he : (fun y => dcLinear (normEnergy n) y a) =
        (fun y => (-1 / 2 : ℂ) * (inner ℝ (I • a) y : ℂ)) := by
      funext y
      rw [dcLinear_apply, dc_normEnergy, real_inner_comm]
    rw [he]
    have hh := ((Complex.ofRealCLM.comp (innerSL ℝ (I • a))).hasFDerivAt (x := x)).const_mul (-1 / 2 : ℂ)
    change HasFDerivAt (fun y => (-1 / 2 : ℂ) * (inner ℝ (I • a) y : ℂ)) _ x at hh
    rw [hh.fderiv]
    simp [real_inner_comm]
  rw [hd, hd, real_inner_complexStructure_swap v w, Complex.ofReal_neg]
  have he : -(inner ℝ v (I • w)) = ∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re) := by
    simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [← he, Complex.ofReal_neg]
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_NormExteriorPower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma alternatingMap_sum_apply {T : Type*} [AddCommGroup T] [Module ℝ T]
    {ι J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ) (v : ι → T) :
    (∑ j ∈ s, a j) v = ∑ j ∈ s, a j v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    change a j v + (∑ i ∈ s, a i) v = _
    rw [ih]

lemma extDeriv_normEnergy_covectors {n : ℕ} (x : ComplexEuclidean n) :
    (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap =
      ∑ j : Fin n, covectorVolume (coordinatePair j) := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [alternatingMap_sum_apply]
  change extDeriv (oneForm (dcLinear (normEnergy n))) x v = _
  rw [hv, extDeriv_dc_normEnergy]
  simp only [covectorVolume_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro coordinate hcoordinate
  simp only [Matrix.det_fin_two, Matrix.of_apply, coordinatePair,
    Matrix.cons_val_zero, Matrix.cons_val_one, realCoordinate_apply, imagCoordinate_apply,
    Complex.ofReal_sub, Complex.ofReal_mul]

/-- Full squared-norm exterior normalization, in arbitrary dimension, for the
actual exterior derivative and standard shuffle powers. -/
theorem extDeriv_normEnergy_top (n : ℕ) (x : ComplexEuclidean n) :
    wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap n =
      (n.factorial : ℂ) • interleavedVolume n := by
  rw [extDeriv_normEnergy_covectors, wedgePower_sum_pairs_top]
  rfl

/-- The normalization is positive on dx_1,dy_1,..., not just determined up
to an unspecified orientation sign. -/
theorem interleavedVolume_basis (n : ℕ) : interleavedVolume n interleavedBasis = 1 := by
  rw [interleavedVolume, covectorVolume_apply]
  have hm : Matrix.of (fun a b : WedgePowerSlots n =>
      pairedCovectors (coordinatePair (n := n)) b (interleavedBasis a)) =
      (1 : Matrix (WedgePowerSlots n) (WedgePowerSlots n) ℂ) := by
    ext a b
    obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv n a = (i,α) := ⟨_,_,rfl⟩
    obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv n b = (j,β) := ⟨_,_,rfl⟩
    have hab : a = b ↔ i = j ∧ α = β := by
      rw [← (pairSlotEquiv n).injective.eq_iff, ha, hb, Prod.mk.injEq]
    fin_cases α <;> fin_cases β <;>
      simp [pairedCovectors, interleavedBasis, ha, hb, coordinatePair,
        Matrix.of_apply, Matrix.one_apply, hab, eq_comm] <;> split_ifs <;> simp_all
  rw [hm, Matrix.det_one]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_OrientedSphereDensity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory Metric

namespace Mahler

section Cofactors
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}

lemma orientedDensity_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) (c : ℂ) :
    orientedDensity b Ω (c • B) x = c * orientedDensity b Ω B x := by
  unfold orientedDensity
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma normalWedge_basis (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    normalWedge x B b =
      ∑ i : Fin (d+1), (b.repr x i : ℂ) * (-1 : ℂ)^i.val * B (i.removeNth b) := by
  rw [normalWedge, AlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [LinearMap.smulRight_apply, AlternatingMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, OrthonormalBasis.repr_apply_apply,
    real_inner_comm x (b i), Complex.real_smul, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  ring

lemma orientedDensity_eq_normalWedge (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    orientedDensity b Ω B x = normalWedge x B b / Ω b := by
  rw [normalWedge_basis]; rfl

/-- On a unit sphere, the normal wedge evaluates on outward normal followed
by tangent vectors as exactly the boundary form. This checks the sign and
shows which surface restriction the cofactor formula represents. -/
theorem normalWedge_outward_tangent (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) {x : E}
    (hx : ‖x‖ = 1) (v : Fin d → E) (hv : ∀ i, inner ℝ x (v i) = 0) :
    normalWedge x B (Matrix.vecCons x v) = B v := by
  rw [normalWedge, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have hzero : (∑ i : Fin d, (-1 : ℤ)^i.succ.val •
      ((innerSL ℝ x).toLinearMap.smulRight B) (Matrix.vecCons x v i.succ)
        (i.succ.removeNth (Matrix.vecCons x v))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Matrix.vecCons, LinearMap.smulRight_apply, hv i]
  rw [hzero]
  simp [LinearMap.smulRight_apply, hx, Matrix.vecCons]

lemma topForm_ext_on_basis (b : Module.Basis (Fin (d+1)) ℝ E)
    {A C : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ} (h : A b = C b) : A = C := by
  classical
  apply b.ext_alternating
  intro v hv
  let e : Equiv.Perm (Fin (d+1)) := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  change A (b ∘ e) = C (b ∘ e)
  rw [A.map_perm, C.map_perm, h]

lemma normalWedge_eq_density_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    normalWedge x B = orientedDensity b Ω B x • Ω := by
  apply topForm_ext_on_basis b.toBasis
  change normalWedge x B b = orientedDensity b Ω B x * Ω b
  rw [orientedDensity_eq_normalWedge, div_mul_cancel₀ _ hΩ]

/-- The density multiplies the outward area form to give the actual
restriction of B to every tuple of tangent vectors. -/
theorem orientedDensity_spec (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) {x : E} (hx : ‖x‖ = 1)
    (v : Fin d → E) (hv : ∀ i, inner ℝ x (v i) = 0) :
    B v = orientedDensity b Ω B x * Ω (Matrix.vecCons x v) := by
  rw [← normalWedge_outward_tangent B hx v hv, normalWedge_eq_density_smul b Ω hΩ]
  rfl

end Cofactors

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereFluxIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric
open scoped BigOperators

namespace Mahler

lemma topForm_basis_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    {Ω : E [⋀^Fin d]→ₗ[ℝ] ℂ} (hΩ : Ω ≠ 0) : Ω b ≠ 0 := by
  classical
  intro hz
  apply hΩ
  apply b.ext_alternating
  intro v hv
  let e : Equiv.Perm (Fin d) := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  change Ω (b ∘ e) = 0
  rw [Ω.map_perm, hz, smul_zero]

lemma sphereVolume_frame_ne_zero (k : ℕ) : sphereVolume k (sphereFrame k) ≠ 0 := by
  apply topForm_basis_ne_zero (sphereFrame k).toBasis
  intro hz
  have h := congrArg (fun a => a (interleavedBasis ∘ (ambientFinEquiv k).symm)) hz
  have he : ((interleavedBasis ∘ (ambientFinEquiv k).symm) ∘ ambientFinEquiv k) =
      (interleavedBasis : WedgePowerSlots (k+1) → ComplexEuclidean (k+1)) := by
    funext i; simp
  simp only [sphereVolume, AlternatingMap.domDomCongr_apply, he,
    interleavedVolume_basis, AlternatingMap.zero_apply] at h
  exact one_ne_zero h

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereVolumeOrientation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler

/-- The cofactor frame is the actual interleaved real orthonormal coordinate
frame, with the same index equivalence used for the volume form. -/
lemma sphereFrame_interleaved (k : ℕ) (s : WedgePowerSlots (k+1)) :
    sphereFrame k (ambientFinEquiv k s) = interleavedBasis s := by
  simp only [sphereFrame, OrthonormalBasis.reindex_apply,
    Pi.orthonormalBasis_apply]
  obtain ⟨j,α,h⟩ : ∃ j α, pairSlotEquiv (k+1) s = (j,α) := ⟨_,_,rfl⟩
  fin_cases α <;> simp [interleavedBasis, h, Complex.coe_orthonormalBasisOneI]

/-- The volume form evaluates to +1 on a real orthonormal frame.
This verifies its Euclidean metric normalization as well as its sign. -/
theorem sphereVolume_orthonormalFrame (k : ℕ) : sphereVolume k (sphereFrame k) = 1 := by
  rw [sphereVolume, AlternatingMap.domDomCongr_apply]
  have he : sphereFrame k ∘ ambientFinEquiv k = interleavedBasis :=
    funext (sphereFrame_interleaved k)
  rw [he, interleavedVolume_basis]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExactFormCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff
namespace Mahler

lemma fluxCoordinates_basis (k : ℕ) (i : Fin ((2*k+1)+1)) :
    fluxCoordinates k (MahlerStokes.coordinateBasis ((2*k+1)+1) i) = sphereFrame k i := by
  apply (sphereFrame k).repr.injective
  simp [fluxCoordinates, MahlerStokes.coordinateBasis, OrthonormalBasis.repr_self]

lemma fluxCoordinates_repr (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    (sphereFrame k).repr (fluxCoordinates k x) = WithLp.toLp 2 x := by
  simp [fluxCoordinates]

lemma norm_fluxCoordinates_sq (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    ‖fluxCoordinates k x‖^2 = MahlerStokes.radiusSq x := by
  rw [MahlerStokes.radiusSq_eq_euclidean_norm_sq]
  exact congrArg (fun t : ℝ => t^2) ((sphereFrame k).repr.symm.norm_map _)

/-- Exterior differentiation commutes with taking the real part; C1 supplies
only the first derivative used here. -/
theorem extDeriv_realForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {eta : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (h : DifferentiableAt ℝ eta x) :
    extDeriv (fun y => realFormCLM E q (eta y)) x =
      realFormCLM E (q+1) (extDeriv eta x) := by
  ext v
  change (ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (fun y => realFormCLM E q (eta y)) x)) v =
      ((ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ eta x)) v).re
  have hd : fderiv ℝ (fun y => realFormCLM E q (eta y)) x =
      (realFormCLM E q).comp (fderiv ℝ eta x) := by
    simpa only [Function.comp_def] using ((realFormCLM E q).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  rw [hd]
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.comp_apply, realFormCLM_apply]
  change _ = Complex.reCLM (∑ i : Fin (q+1), (-1 : ℤ)^i.val •
    fderiv ℝ eta x (v i) (i.removeNth v))
  simp only [map_sum, map_zsmul]
  rfl

lemma contDiffOn_fluxPullback {k q : ℕ} {s : ℕ∞ω}
    {eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    {U : Set (ComplexEuclidean (k+1))} (h : ContDiffOn ℝ s eta U) :
    ContDiffOn ℝ s (fluxPullback eta) ((fluxCoordinates k) ⁻¹' U) := by
  exact (realFormCLM _ q).contDiff.comp_contDiffOn
    ((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (fluxCoordinates k).toContinuousLinearMap).contDiff.comp_contDiffOn
      (h.comp (fluxCoordinates k).contDiff.contDiffOn (fun _ hx => hx)))

/-- Naturality for the actual fixed linear coordinates, requiring only a
first derivative of eta. The coordinate map itself is smooth. -/
theorem extDeriv_fluxPullback {k q : ℕ}
    {eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    {x : Fin ((2*k+1)+1) → ℝ} (h : DifferentiableAt ℝ eta (fluxCoordinates k x)) :
    extDeriv (fluxPullback eta) x = fluxPullback (extDeriv eta) x := by
  have hp : DifferentiableAt ℝ (fun y => (eta (fluxCoordinates k y)).compContinuousLinearMap
      (fluxCoordinates k).toContinuousLinearMap) x :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (fluxCoordinates k).toContinuousLinearMap (ι := Fin q) (F := ℂ)).differentiableAt.comp x
      (h.comp x (fluxCoordinates k).differentiableAt)
  change extDeriv (fun y => realFormCLM _ q
    ((eta (fluxCoordinates k y)).compContinuousLinearMap (fluxCoordinates k).toContinuousLinearMap)) x = _
  rw [extDeriv_realForm hp]
  have hn := extDeriv_pullback h ((fluxCoordinates k).contDiff.contDiffAt (n := 2)) (by simp)
  simpa only [ContinuousLinearEquiv.fderiv, fluxPullback] using congrArg (realFormCLM _ (q+1)) hn

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma radiusSq_smul {n : ℕ} (r : ℝ) (x : Fin n → ℝ) :
    radiusSq (r • x) = r^2 * radiusSq x := by
  simp only [radiusSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma chord_pos {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    0 < chord 1 y := Real.sqrt_pos.2 (sub_pos.mpr hy)

lemma radiusSq_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) : radiusSq (hemisphereCone i x) = (x i)^2 := by
  rw [hemisphereCone, radiusSq_smul, radiusSq_hemisphereGraph i hx.2, mul_one]

lemma hemisphereCone_injOn {n : ℕ} (i : Fin (n+1)) :
    InjOn (hemisphereCone i) (hemisphereConeDomain i) := by
  intro x hx y hy h
  have hr : x i = y i := (sq_eq_sq₀ hx.1.1.le hy.1.1.le).mp
    ((radiusSq_hemisphereCone i hx).symm.trans ((congrArg radiusSq h).trans
      (radiusSq_hemisphereCone i hy)))
  have hv : i.removeNth x = i.removeNth y := by
    funext j
    have hj := congrFun h (i.succAbove j)
    simp only [hemisphereCone, hemisphereGraph, Pi.smul_apply, smul_eq_mul,
      Fin.insertNth_apply_succAbove] at hj
    rw [hr] at hj
    exact mul_left_cancel₀ hy.1.1.ne' hj
  apply funext
  rw [i.forall_iff_succAbove]
  exact ⟨hr, fun k => congrFun hv k⟩

lemma hasFDerivAt_radiusSq {n : ℕ} (y : Fin n → ℝ) :
    HasFDerivAt radiusSq (2 • coordinateDot y) y := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := y)).pow 2)
  convert! h using 1
  ext v
  simp [coordinateDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hasFDerivAt_chord {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    HasFDerivAt (chord 1) (chordDerivative y) y := by
  have h := ((hasFDerivAt_radiusSq y).const_sub (1^2)).sqrt (sub_pos.mpr hy).ne'
  convert! h using 1
  ext v
  simp [chordDerivative, chord]
  ring

lemma hasFDerivAt_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) :
    HasFDerivAt (hemisphereGraph i) (hemisphereGraphDerivative i y) y := by
  apply hasFDerivAt_pi.2
  rw [i.forall_iff_succAbove]
  constructor
  · simpa [hemisphereGraph, hemisphereGraphDerivative] using hasFDerivAt_chord hy
  · intro j
    simp only [hemisphereGraph, Fin.insertNth_apply_succAbove]
    exact hasFDerivAt_apply j y

lemma hasFDerivAt_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) :
    HasFDerivAt (hemisphereCone i) (hemisphereConeDerivative i x) x := by
  exact (ContinuousLinearMap.proj i : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.smul
    ((hasFDerivAt_hemisphereGraph i hx.2).comp x (removeCoordinate i).hasFDerivAt)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma det_hemisphereFrameMatrix {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    (hemisphereFrameMatrix y).det = (chord 1 y)⁻¹ := by
  change (Matrix.fromBlocks (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => chord 1 y))
    (Matrix.of (fun _ j => -(chord 1 y)⁻¹ * y j))
    (Matrix.of (fun j _ => y j)) (1 : Matrix (Fin n) (Fin n) ℝ)).det = _
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply]
  have hs : (∑ j, (-(chord 1 y)⁻¹ * y j) * y j) =
      -(chord 1 y)⁻¹ * radiusSq y := by
    rw [radiusSq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  have hc := chord_sq hy
  have hn := (chord_pos hy).ne'
  field_simp
  nlinarith

lemma hemisphereConeDerivative_matrix {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (LinearMap.toMatrix' (hemisphereConeDerivative i x).toLinearMap).submatrix
      (splitCoordinate i) (splitCoordinate i) =
    Matrix.updateCol (x i • hemisphereFrameMatrix (i.removeNth x)) (Sum.inl 0)
      (fun j => hemisphereFrameMatrix (i.removeNth x) j (Sum.inl 0)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals try (have hb : b = (0 : Fin 1) := Subsingleton.elim _ _; subst b)
  all_goals
    simp [LinearMap.toMatrix'_apply, hemisphereConeDerivative,
      hemisphereGraphDerivative, removeCoordinate, hemisphereGraph, chordDerivative,
      coordinateDot, hemisphereFrameMatrix, Matrix.updateCol, Matrix.fromBlocks,
      Fin.removeNth, Pi.single_apply, Function.update,
      Fin.ne_succAbove, eq_comm, mul_comm, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The actual ambient Jacobian of radial hemisphere coordinates. The
singularity is only at the equator, outside the open parameter domain. -/
theorem det_hemisphereConeDerivative {n : ℕ} (i : Fin (n+1))
    {x : Fin (n+1) → ℝ} (hx : x ∈ hemisphereConeDomain i) :
    (hemisphereConeDerivative i x).toLinearMap.det =
      (x i)^n * (chord 1 (i.removeNth x))⁻¹ := by
  rw [← LinearMap.det_toMatrix', ← Matrix.det_submatrix_equiv_self (splitCoordinate i),
    hemisphereConeDerivative_matrix, Matrix.det_updateCol_smul_left,
    Matrix.updateCol_eq_self, det_hemisphereFrameMatrix hx.2]
  simp

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace MahlerStokes

/-- Nonnegative Fubini in the distinguished coordinate; no integrability
assumption is needed for the singular hemisphere area density. -/
theorem setLIntegral_slice {n : ℕ} (i : Fin (n+1)) {s : Set (Fin (n+1) → ℝ)}
    (hs : MeasurableSet s) (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in s, f x) = ∫⁻ y : Fin n → ℝ,
      ∫⁻ t in {t | i.insertNth t y ∈ s}, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  calc
    (∫⁻ x in s, f x) = ∫⁻ p : ℝ × (Fin n → ℝ), s.indicator f (i.insertNth p.1 p.2) := by
      rw [← lintegral_indicator hs]
      exact (hp.lintegral_comp_emb e.symm.measurableEmbedding (s.indicator f)).symm
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ t : ℝ, s.indicator f (i.insertNth t y) := by
      exact (lintegral_prod _ ((hf.indicator hs).comp e.symm.measurable).aemeasurable).trans
        (lintegral_lintegral_swap ((hf.indicator hs).comp e.symm.measurable).aemeasurable)
    _ = _ := by
      apply lintegral_congr
      intro y
      change _ = ∫⁻ t in (fun t : ℝ => i.insertNth t y) ⁻¹' s, f (i.insertNth t y)
      rw [← lintegral_indicator (hs.preimage (by fun_prop : Measurable (fun t : ℝ => i.insertNth t y)))]
      rfl

lemma lintegral_pow_unitInterval (n : ℕ) :
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t^n)) =
      ENNReal.ofReal ((n+1 : ℝ)⁻¹) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal ((continuous_pow n).intervalIntegrable (0 : ℝ) 1).1]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le n

lemma measurableSet_coneStrip {n : ℕ} (i : Fin (n+1)) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) : MeasurableSet (coneStrip i S) :=
  ((measurable_pi_apply i) measurableSet_Ioo).inter ((removeCoordinate i).measurable hS)

lemma coneStrip_subset {n : ℕ} (i : Fin (n+1)) {S : Set (Fin n → ℝ)}
    (hS : S ⊆ coordBall n 1) : coneStrip i S ⊆ hemisphereConeDomain i :=
  fun _ hx => ⟨hx.1, hS hx.2⟩

/-- Integrating the exact radial Jacobian leaves the hemisphere area density,
with the inverse dimension factor appearing in the cone definition of area. -/
theorem volume_hemisphereCone_strip {n : ℕ} (i : Fin (n+1))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hSB : S ⊆ coordBall n 1) :
    volume (hemisphereCone i '' coneStrip i S) =
      ENNReal.ofReal ((n+1 : ℝ)⁻¹) * ∫⁻ y in S, ENNReal.ofReal (chord 1 y)⁻¹ := by
  have hs := measurableSet_coneStrip i hS
  have hsub := coneStrip_subset i hSB
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun x hx => (hasFDerivAt_hemisphereCone i (hsub hx)).hasFDerivWithinAt)
    ((hemisphereCone_injOn i).mono hsub)]
  have he : (∫⁻ x in coneStrip i S, ENNReal.ofReal |(hemisphereConeDerivative i x).det|) =
      ∫⁻ x in coneStrip i S,
        ENNReal.ofReal ((x i)^n) * ENNReal.ofReal (chord 1 (i.removeNth x))⁻¹ := by
    apply setLIntegral_congr_fun hs
    intro x hx
    change ENNReal.ofReal |(hemisphereConeDerivative i x).toLinearMap.det| = _
    rw [det_hemisphereConeDerivative i (hsub hx), abs_of_pos
      (mul_pos (pow_pos hx.1.1 _) (inv_pos.2 (chord_pos (hSB hx.2)))),
      ENNReal.ofReal_mul (pow_nonneg hx.1.1.le n)]
  rw [he, setLIntegral_slice i hs _ (by unfold chord radiusSq Fin.removeNth; fun_prop)]
  rw [← lintegral_indicator hS, ← lintegral_const_mul _ (by unfold chord radiusSq; fun_prop)]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ S
  · have ht : {t : ℝ | i.insertNth t y ∈ coneStrip i S} = Ioo 0 1 := by
      ext t; simp [coneStrip, hy]
    simp only [ht, Fin.insertNth_apply_same, Fin.removeNth_insertNth,
      indicator_of_mem hy]
    rw [lintegral_mul_const _ (by fun_prop), lintegral_pow_unitInterval]
  · have ht : {t : ℝ | i.insertNth t y ∈ coneStrip i S} = ∅ := by
      ext t; simp [coneStrip, hy]
    simp [ht, hy]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereArea
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
open scoped ENNReal Pointwise
namespace MahlerStokes

lemma continuous_hemisphereGraph {n : ℕ} (i : Fin (n+1)) : Continuous (hemisphereGraph i) := by
  unfold hemisphereGraph chord radiusSq
  fun_prop

lemma continuous_hemisphereParam {n : ℕ} (i : Fin (n+1)) : Continuous (hemisphereParam i) := by
  apply continuous_induced_rng.2
  exact (PiLp.continuous_toLp 2 _).comp ((continuous_hemisphereGraph i).comp continuous_subtype_val)

lemma hemisphereParam_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (hemisphereParam i) := by
  intro y z h
  apply Subtype.ext
  funext j
  have he := congrArg (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
    (w : EuclideanSpace ℝ (Fin (n+1))) (i.succAbove j)) h
  simpa [hemisphereParam, hemisphereGraph] using he

lemma hemisphereParam_range {n : ℕ} (i : Fin (n+1)) :
    range (hemisphereParam i) =
      {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 | 0 < (z : EuclideanSpace ℝ (Fin (n+1))) i} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    simpa [hemisphereParam, hemisphereGraph] using chord_pos y.property
  · intro hz
    let x : Fin (n+1) → ℝ := ofLp (z : EuclideanSpace ℝ (Fin (n+1)))
    have hnorm : ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using z.property
    have hr : radiusSq x = 1 := by rw [radiusSq_eq_euclidean_norm_sq]; simp [x, hnorm]
    have hs : radiusSq x = (x i)^2 + radiusSq (i.removeNth x) := by
      have he : i.insertNth (x i) (i.removeNth x) = x := by simp
      rw [← he, radiusSq_insertNth]; simp
    have hi : 0 < x i := hz
    have hy : i.removeNth x ∈ coordBall n 1 := by
      change radiusSq (i.removeNth x) < 1^2
      nlinarith
    have hc : chord 1 (i.removeNth x) = x i := by
      apply (sq_eq_sq₀ (chord_pos hy).le hi.le).1
      rw [chord_sq hy]
      linarith
    refine ⟨⟨i.removeNth x, hy⟩, ?_⟩
    apply Subtype.ext
    change toLp 2 (hemisphereGraph i (i.removeNth x)) = toLp 2 x
    congr 1
    simp [hemisphereGraph, hc]

lemma hemisphereParam_measurableEmbedding {n : ℕ} (i : Fin (n+1)) :
    MeasurableEmbedding (hemisphereParam i) := by
  let := (measurableSet_coordBall n 1).standardBorel
  exact (continuous_hemisphereParam i).measurable.measurableEmbedding (hemisphereParam_injective i)

lemma hemisphereCone_image_toLp {n : ℕ} (i : Fin (n+1)) (S : Set (Fin n → ℝ)) :
    (toLp 2 : (Fin (n+1) → ℝ) → EuclideanSpace ℝ (Fin (n+1))) ''
      (hemisphereCone i '' coneStrip i S) =
    Ioo (0 : ℝ) 1 • ((fun y => (toLp 2 (hemisphereGraph i y) : EuclideanSpace ℝ (Fin (n+1)))) '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x i, hx.1, toLp 2 (hemisphereGraph i (i.removeNth x)),
      ⟨i.removeNth x, hx.2, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨hemisphereCone i (i.insertNth r y), ⟨i.insertNth r y, ?_, rfl⟩, ?_⟩
    · simpa [coneStrip] using And.intro hr hy
    · simp [hemisphereCone]

lemma volume_toLp_image {n : ℕ} (S : Set (Fin n → ℝ)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (toLp 2 '' S) = volume S := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have h := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' S)
  change volume (e ⁻¹' (e '' S)) = volume (e '' S) at h
  rw [e.injective.preimage_image] at h
  exact h.symm

/-- The hemisphere chart pushes forward exactly the reciprocal-chord area
measure. This is proved from the cone definition of volume.toSphere. -/
theorem toSphere_hemisphereParam_image {n : ℕ} (i : Fin (n+1))
    {S : Set (coordBall n 1)} (hS : MeasurableSet S) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere (hemisphereParam i '' S) =
      ∫⁻ y in (Subtype.val '' S), ENNReal.ofReal (chord 1 y)⁻¹ := by
  have hm := (hemisphereParam_measurableEmbedding i).measurableSet_image.mpr hS
  rw [Measure.toSphere_apply' _ hm]
  have he : Subtype.val '' (hemisphereParam i '' S) =
      (fun y => (toLp 2 (hemisphereGraph i y) : EuclideanSpace ℝ (Fin (n+1)))) '' (Subtype.val '' S) := by
    rw [← image_comp, image_image]
    rfl
  rw [he, ← hemisphereCone_image_toLp, volume_toLp_image,
    volume_hemisphereCone_strip i
      ((MeasurableEmbedding.subtype_coe (measurableSet_coordBall n 1)).measurableSet_image.mpr hS)
      (by rintro y ⟨z, hz, rfl⟩; exact z.property)]
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  rw [hd, ← mul_assoc]
  have hc : (↑(n+1) : ℝ≥0∞) * ENNReal.ofReal ((n+1 : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    push_cast
    rw [mul_inv_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)]
    simp
  rw [hc, one_mul]

lemma measurableSet_hemisphereRange {n : ℕ} (i : Fin (n+1)) :
    MeasurableSet (range (hemisphereParam i)) :=
  (hemisphereParam_measurableEmbedding i).measurableSet_range

/-- Full measure equality, sufficient for Bochner as well as nonnegative
integration. No sphere integration identity is a premise. -/
theorem measurePreserving_hemisphereParam {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (hemisphereParam i) (hemisphereParameterArea n)
      ((volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere.restrict
        (range (hemisphereParam i))) := by
  refine ⟨(continuous_hemisphereParam i).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_hemisphereParam i).measurable hs,
    hemisphereParameterArea, withDensity_apply _ ((continuous_hemisphereParam i).measurable hs),
    setLIntegral_subtype (measurableSet_coordBall n 1) _
      (fun y : Fin n → ℝ => ENNReal.ofReal (chord 1 y)⁻¹),
    Measure.restrict_apply hs]
  rw [← toSphere_hemisphereParam_image i ((continuous_hemisphereParam i).measurable hs),
    image_preimage_eq_inter_range]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- The positive normal coordinate cancels the reciprocal-chord surface
Jacobian, giving exactly the coordinate hemisphere integral used by Stokes. -/
theorem integral_upperHemisphere {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) :
    (∫ z in range (hemisphereParam i),
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1, f (toLp 2 (hemisphereGraph i y)) := by
  have hw : Measurable (fun y : coordBall n 1 => ENNReal.ofReal ((chord 1 (y : Fin n → ℝ))⁻¹)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.inv
    exact ((show Continuous (chord (n := n) 1) by unfold chord radiusSq; fun_prop).comp continuous_subtype_val).measurable
  rw [← (measurePreserving_hemisphereParam i).integral_comp
    (hemisphereParam_measurableEmbedding i)
    (fun z => (z : EuclideanSpace ℝ (Fin (n+1))) i * f z),
    hemisphereParameterArea, integral_withDensity_eq_integral_toReal_smul
      hw (by simp)]
  calc
    _ = ∫ y : coordBall n 1, f (toLp 2 (hemisphereGraph i y)) ∂volume.comap Subtype.val := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hc := chord_pos y.property
      simp [hemisphereParam, hemisphereGraph, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le),
        smul_eq_mul, hc.ne']
    _ = _ := integral_subtype_comap (measurableSet_coordBall n 1) (fun y => f (toLp 2 (hemisphereGraph i y)))

lemma coordBall_neg_preimage (n : ℕ) :
    (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' coordBall n 1 = coordBall n 1 := by
  ext y
  simp [coordBall, radiusSq]

lemma neg_hemisphereGraph {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    -(hemisphereGraph i y) = i.insertNth (-chord 1 (-y)) (-y) := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp [hemisphereGraph, chord, radiusSq]
  · intro j; simp [hemisphereGraph]

/-- Lower hemisphere, with the negative normal coordinate and the same
positive coordinate measure on the parameter ball. -/
theorem integral_lowerHemisphere {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) :
    (∫ z in {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
        (z : EuclideanSpace ℝ (Fin (n+1))) i < 0},
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    -(∫ y in coordBall n 1, f (toLp 2 (i.insertNth (-chord 1 y) y))) := by
  let e := sphereIsometry (LinearIsometryEquiv.neg ℝ :
    EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
  have hp := measurePreserving_sphereIsometry
    (LinearIsometryEquiv.neg ℝ : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] _) volume volume
    (LinearIsometryEquiv.neg ℝ).measurePreserving
  have hpre : e ⁻¹' {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
      (z : EuclideanSpace ℝ (Fin (n+1))) i < 0} = range (hemisphereParam i) := by
    rw [hemisphereParam_range]
    ext z
    simp [e, sphereIsometry]
  have hi := hp.setIntegral_preimage_emb e.measurableEmbedding
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z)
    {z | (z : EuclideanSpace ℝ (Fin (n+1))) i < 0}
  rw [hpre] at hi
  rw [← hi]
  have he : (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (e z : EuclideanSpace ℝ (Fin (n+1))) i * f (e z)) =
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 => -((z : EuclideanSpace ℝ (Fin (n+1))) i * f (-(z : EuclideanSpace ℝ (Fin (n+1)))))) := by
    funext z
    simp [e, sphereIsometry]
  rw [he, integral_neg, integral_upperHemisphere i (fun z => f (-z))]
  congr 1
  have hnegPi : MeasurePreserving (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) :=
    volume_preserving_pi (fun _ : Fin n =>
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving)
  have hb := hnegPi.setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin n → ℝ)).measurableEmbedding
    (fun y => f (toLp 2 (i.insertNth (-chord 1 y) y))) (coordBall n 1)
  rw [coordBall_neg_preimage] at hb
  convert! hb using 1
  apply setIntegral_congr_fun (measurableSet_coordBall n 1)
  intro y _
  dsimp only
  rw [← neg_hemisphereGraph]
  rfl

lemma integral_sphere_coordinate_of_integrable {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hf : Integrable (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z)
      (volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere)
    (hp : IntegrableOn (fun y => f (toLp 2 (hemisphereGraph i y))) (coordBall n 1))
    (hm : IntegrableOn (fun y => f (toLp 2 (i.insertNth (-chord 1 y) y))) (coordBall n 1)) :
    (∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1,
      f (toLp 2 (i.insertNth (chord 1 y) y)) - f (toLp 2 (i.insertNth (-chord 1 y) y)) := by
  have hneg : MeasurableSet {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
      (z : EuclideanSpace ℝ (Fin (n+1))) i < 0} := by
    exact isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have he : (∫ z in (range (hemisphereParam i))ᶜ,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
      ∫ z in {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 | (z : EuclideanSpace ℝ (Fin (n+1))) i < 0},
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
    rw [← integral_indicator (measurableSet_hemisphereRange i).compl, ← integral_indicator hneg]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : (z : EuclideanSpace ℝ (Fin (n+1))) i < 0
    · have hn : ¬0 < (z : EuclideanSpace ℝ (Fin (n+1))) i := by linarith
      simp [hemisphereParam_range, hz, hn]
    · by_cases hp : 0 < (z : EuclideanSpace ℝ (Fin (n+1))) i
      · simp [hemisphereParam_range, hp, hz]
      · have hzero : (z : EuclideanSpace ℝ (Fin (n+1))) i = 0 := by linarith
        simp [hzero]
  rw [← integral_add_compl (measurableSet_hemisphereRange i) hf, he,
    integral_upperHemisphere, integral_lowerHemisphere, ← sub_eq_add_neg, ← integral_sub hp hm]
  rfl

lemma mem_unitSphere_of_radiusSq {n : ℕ} {x : Fin n → ℝ} (hx : radiusSq x = 1) :
    (toLp 2 x : EuclideanSpace ℝ (Fin n)) ∈ sphere 0 1 := by
  simp only [mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← radiusSq_eq_euclidean_norm_sq, hx, one_pow]

/-- Continuity only on the sphere supplies every integrability premise.
The integrand may be singular at the origin. -/
theorem integral_sphere_coordinate {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hf : ContinuousOn f (sphere 0 1)) :
    (∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1,
      f (toLp 2 (i.insertNth (chord 1 y) y)) - f (toLp 2 (i.insertNth (-chord 1 y) y)) := by
  apply integral_sphere_coordinate_of_integrable i f
  · let : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
    have hc : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (z : EuclideanSpace ℝ (Fin (n+1))) i * f z) :=
      (by fun_prop : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (z : EuclideanSpace ℝ (Fin (n+1))) i)).mul (hf.comp_continuous continuous_subtype_val (fun z => z.property))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · refine IntegrableOn.mono_set (s := coordBall n 1) (t := coordClosedBall n 1) ?_
      (fun y hy => (show radiusSq y < 1^2 from hy).le)
    apply ContinuousOn.integrableOn_compact (isCompact_coordClosedBall n 1)
    apply hf.comp ((PiLp.continuous_toLp 2 _).comp (continuous_hemisphereGraph i)).continuousOn
    intro y hy
    apply mem_unitSphere_of_radiusSq
    simpa [hemisphereGraph] using (radiusSq_boundary i 1 hy).1
  · refine IntegrableOn.mono_set (s := coordBall n 1) (t := coordClosedBall n 1) ?_
      (fun y hy => (show radiusSq y < 1^2 from hy).le)
    apply ContinuousOn.integrableOn_compact (isCompact_coordClosedBall n 1)
    apply hf.comp (show Continuous (fun y : Fin n → ℝ =>
      (toLp 2 (i.insertNth (-chord 1 y) y) : EuclideanSpace ℝ (Fin (n+1)))) by
        unfold chord radiusSq; fun_prop).continuousOn
    intro y hy
    apply mem_unitSphere_of_radiusSq
    simpa using (radiusSq_boundary i 1 hy).2

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereCoordinateIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

lemma continuousOn_sphere_coefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = 1}) (i : Fin (n+1)) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n+1)) =>
      ω (ofLp z) (i.removeNth (coordinateBasis (n+1)))) (sphere 0 1) := by
  have hw : ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n+1)) => ω (ofLp z)) (sphere 0 1) := by
    apply hω.comp (PiLp.continuous_ofLp 2 _).continuousOn
    intro z hz
    change radiusSq (ofLp z) = 1
    rw [radiusSq_eq_euclidean_norm_sq]
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    simp [hn]
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (coordinateBasis (n+1)))).continuous.comp_continuousOn hw

/-- Exact equality of the hemisphere-coordinate Stokes integral and the
outward cofactor density integrated against volume.toSphere. -/
theorem sphereFlux_unit_eq_areaIntegral {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = 1}) :
    sphereFlux 1 ω =
      ∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
        coordinateSphereDensity 1 ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
  let : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hc (i : Fin (n+1)) : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (-1 : ℝ)^i.val * (z : EuclideanSpace ℝ (Fin (n+1))) i *
      ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1)))) (i.removeNth (coordinateBasis (n+1)))) :=
    ((continuous_const.mul (by fun_prop)).mul
      ((continuousOn_sphere_coefficient ω hω i).comp_continuous continuous_subtype_val (fun z => z.property)))
  simp only [coordinateSphereDensity, one_smul]
  rw [integral_finsetSum _ (fun i _ =>
    (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  unfold sphereFlux
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_sphere_coordinate i _ (continuousOn_sphere_coefficient ω hω i)]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExactSphereFluxBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators
namespace Mahler

/-- The real coordinate cofactor sum is the actual complex sphereFlux density.
The volume of the chosen frame is +1, so no orientation or normalization factor remains. -/
theorem coordinateSphereDensity_fluxPullback {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (x : Fin ((2*k+1)+1) → ℝ) :
    MahlerStokes.coordinateSphereDensity 1 (fluxPullback B) x =
      (orientedDensity (sphereFrame k) (sphereVolume k)
        (B (fluxCoordinates k x)).toAlternatingMap (fluxCoordinates k x)).re := by
  classical
  unfold MahlerStokes.coordinateSphereDensity orientedDensity
  rw [sphereVolume_orthonormalFrame, div_one]
  simp only [one_smul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : (fluxCoordinates k).toContinuousLinearMap ∘
      i.removeNth (MahlerStokes.coordinateBasis ((2*k+1)+1)) = i.removeNth (sphereFrame k) := by
    funext j
    exact fluxCoordinates_basis k (i.succAbove j)
  simp only [fluxPullback, realFormCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hv, fluxCoordinates_repr]
  have hs : (-1 : ℂ)^i.val = (((-1 : ℝ)^i.val : ℝ) : ℂ) := by push_cast; rfl
  rw [hs]
  simp only [Complex.mul_re, Complex.mul_im, ContinuousAlternatingMap.coe_toAlternatingMap, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

lemma continuousOn_fluxPullback_sphere {k q : ℕ}
    {B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    (hB : ContinuousOn B (sphere 0 1)) :
    ContinuousOn (fluxPullback B) {x | MahlerStokes.radiusSq x = 1} := by
  apply (realFormCLM _ q).continuous.comp_continuousOn
  apply (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (fluxCoordinates k).toContinuousLinearMap).continuous.comp_continuousOn
  apply hB.comp (fluxCoordinates k).continuous.continuousOn
  intro x hx
  simp only [mem_sphere, dist_zero_right]
  have hh := norm_fluxCoordinates_sq k x
  rw [hx] at hh
  nlinarith [norm_nonneg (fluxCoordinates k x)]

/-- The hemisphere-coordinate Stokes flux is exactly Mahler's real flux of a
complex form. Only continuity on the sphere is required. -/
theorem sphereFlux_eq_coordinateFlux {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (hB : ContinuousOn B (sphere 0 1)) :
    sphereFlux k (fun x => (B x).toAlternatingMap) =
      MahlerStokes.sphereFlux 1 (fluxPullback B) := by
  rw [MahlerStokes.sphereFlux_unit_eq_areaIntegral _ (continuousOn_fluxPullback_sphere hB)]
  let e := (sphereFrame k).repr.symm
  have hm := MahlerStokes.measurePreserving_sphereIsometry e volume volume e.measurePreserving
  have he := hm.integral_comp (MahlerStokes.sphereIsometry e).measurableEmbedding
    (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      (orientedDensity (sphereFrame k) (sphereVolume k) (B z).toAlternatingMap z).re)
  unfold sphereFlux sphereArea
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with z
  exact (coordinateSphereDensity_fluxPullback B (WithLp.ofLp z.val)).symm

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExactSphereStokes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology
namespace Mahler

/-- C1 on an open sphere neighborhood supplies all continuity needed by the
area integral. There is no regularity assumption inside the ball. -/
lemma continuousOn_extDeriv_sphere {k q : ℕ}
    {eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    {U : Set (ComplexEuclidean (k+1))} (hU : IsOpen U)
    (hSU : sphere 0 1 ⊆ U) (h : ContDiffOn ℝ 1 eta U) :
    ContinuousOn (extDeriv eta) (sphere 0 1) := by
  intro x hx
  have hd := ((h.contDiffAt (hU.mem_nhds (hSU hx))).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℂ (n := q)).continuous.continuousAt.comp hd).continuousWithinAt

/-- Exact C1 transport to the coordinate sphere. This equality
does not assert that the flux vanishes. -/
theorem sphereFlux_extDeriv_eq_coordinateFlux {k : ℕ}
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k)]→L[ℝ] ℂ)
    {U : Set (ComplexEuclidean (k+1))} (hU : IsOpen U)
    (hSU : sphere 0 1 ⊆ U) (h : ContDiffOn ℝ 1 eta U) :
    sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) =
      MahlerStokes.sphereFlux 1 (extDeriv (fluxPullback eta)) := by
  rw [sphereFlux_eq_coordinateFlux _ (continuousOn_extDeriv_sphere hU hSU h)]
  apply MahlerStokes.sphereFlux_congr
  intro x hx
  have hs : fluxCoordinates k x ∈ sphere (0 : ComplexEuclidean (k+1)) 1 := by
    simp only [mem_sphere, dist_zero_right]
    have hh := norm_fluxCoordinates_sq k x
    have hx' : MahlerStokes.radiusSq x = 1 := by simpa using hx
    rw [hx'] at hh
    nlinarith [norm_nonneg (fluxCoordinates k x)]
  exact (extDeriv_fluxPullback ((h.contDiffAt (hU.mem_nhds (hSU hs))).differentiableAt (by norm_num))).symm

/-- The coordinate Stokes theorem for C2 forms. -/
theorem sphereFlux_extDeriv_eq_zero_of_C2 {k : ℕ}
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k)]→L[ℝ] ℂ)
    {U : Set (ComplexEuclidean (k+1))} (hU : IsOpen U)
    (hSU : sphere 0 1 ⊆ U) (h : ContDiffOn ℝ 2 eta U) :
    sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) = 0 := by
  rw [sphereFlux_extDeriv_eq_coordinateFlux eta hU hSU (h.of_le (by norm_num))]
  apply MahlerStokes.sphereFlux_extDeriv_eq_zero 1
    (hU.preimage (fluxCoordinates k).continuous) _ (fluxPullback eta) (contDiffOn_fluxPullback h)
  intro x hx
  apply hSU
  simp only [mem_sphere, dist_zero_right]
  have hh := norm_fluxCoordinates_sq k x
  have hx' : MahlerStokes.radiusSq x = 1 := by simpa using hx
  rw [hx'] at hh
  nlinarith [norm_nonneg (fluxCoordinates k x)]

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_UnitaryReference
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma normEnergy_twoForm_inner {n : ℕ} (x v w : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v,w] =
      -(inner ℝ v (I • w) : ℂ) := by
  rw [extDeriv_dc_normEnergy]
  have h : (∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re)) =
      -inner ℝ v (I • w) := by
    simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [h, Complex.ofReal_neg]

lemma unitary_real_inner {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (v w : ComplexEuclidean n) :
    inner ℝ (L v) (L w) = inner ℝ v w := by
  let Lr : ComplexEuclidean n ≃ₗᵢ[ℝ] ComplexEuclidean n :=
    { L.toLinearEquiv.restrictScalars ℝ with norm_map' := L.norm_map }
  exact Lr.inner_map_map v w

lemma normEnergy_twoForm_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) :
    (extDeriv (oneForm (dcLinear (normEnergy n))) (L x)).toAlternatingMap.compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap := by
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change extDeriv (oneForm (dcLinear (normEnergy n))) (L x) (fun i => L (![v 0,v 1] i)) = _
  have he : (fun i => L (![v 0,v 1] i)) = ![L (v 0), L (v 1)] := by
    ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (normEnergy n))) (L x) (fun i => L (![v 0,v 1] i)) =
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v 0,v 1]
  rw [he, normEnergy_twoForm_inner, normEnergy_twoForm_inner, ← L.map_smul,
    unitary_real_inner]

/-- Unitary maps preserve the actual positive coordinate volume. The proof
uses the normalized symplectic top power, so no determinant sign is assumed. -/
theorem interleavedVolume_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) :
    (interleavedVolume n).compLinearMap (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      interleavedVolume n := by
  have h := congrArg (fun a => wedgePower a n) (normEnergy_twoForm_unitary L 0)
  rw [← wedgePower_compLinearMap, extDeriv_normEnergy_top, extDeriv_normEnergy_top] at h
  ext v
  have hv := congrArg (fun a => a v) h
  change (n.factorial : ℂ) * interleavedVolume n (fun i => L (v i)) =
    (n.factorial : ℂ) * interleavedVolume n v at hv
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n) hv

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ReferencePoleFrame
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma ambientFinEquiv_real_zero (k : ℕ) :
    ambientFinEquiv k (Sum.inl 0) = 0 := by
  apply Fin.ext
  rfl

lemma ambientFinEquiv_imag_zero (k : ℕ) :
    ambientFinEquiv k (Sum.inl 1) = (boundaryFinEquiv k (Sum.inl 0)).succ := by
  apply Fin.ext
  rfl

lemma ambientFinEquiv_tail (k : ℕ) (s : WedgePowerSlots k) :
    ambientFinEquiv k (Sum.inr s) = (boundaryFinEquiv k (Sum.inr s)).succ := by
  apply Fin.ext
  change 2 + (powerFinEquiv k s).val = (1 + (powerFinEquiv k s).val) + 1
  omega

lemma poleFrameFin_volume (k : ℕ) :
    sphereVolume k (Matrix.vecCons (referencePole k) (poleFrameFin k)) = 1 := by
  have he : (Matrix.vecCons (referencePole k) (poleFrameFin k)) ∘ ambientFinEquiv k =
      (interleavedBasis : WedgePowerSlots (k+1) → ComplexEuclidean (k+1)) := by
    funext s
    cases s with
    | inl j =>
      fin_cases j
      · change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inl 0)) = _
        rw [ambientFinEquiv_real_zero]
        simp [Matrix.vecCons, referencePole, interleavedBasis, pairSlotEquiv]
        rfl
      · change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inl 1)) = _
        rw [ambientFinEquiv_imag_zero]
        simp [Matrix.vecCons, poleFrameFin, interleavedBasis, pairSlotEquiv, poleFrameVector]
        rfl
    | inr s =>
      change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inr s)) = _
      rw [ambientFinEquiv_tail]
      simp [Matrix.vecCons, poleFrameFin, interleavedBasis, pairSlotEquiv, poleFrameVector]
      rfl
  simp only [sphereVolume, AlternatingMap.domDomCongr_apply, he, interleavedVolume_basis]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ReferenceSphereIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric
open scoped BigOperators

namespace Mahler

lemma exists_unitary_referencePole {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1) :
    ∃ L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1), L (referencePole k) = x := by
  classical
  have hv : Orthonormal ℂ (({0} : Set (Fin (k+1))).domRestrict (fun _ => x)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by simpa using i.property.trans j.property.symm)
    simp [hij, Set.domRestrict, inner_self_eq_norm_sq_to_K, hx]
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [ComplexEuclidean])
  refine ⟨b.repr.symm, ?_⟩
  rw [referencePole, b.repr_symm_single]
  exact hb 0 (Set.mem_singleton 0)

lemma sphereVolume_unitary {k : ℕ}
    (L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1))
    (v : Fin ((2*k+1)+1) → ComplexEuclidean (k+1)) :
    sphereVolume k (L ∘ v) = sphereVolume k v := by
  have h := congrArg (fun A => A (v ∘ ambientFinEquiv k)) (interleavedVolume_unitary L)
  simpa only [sphereVolume, AlternatingMap.domDomCongr_apply,
    AlternatingMap.compLinearMap_apply, Function.comp_def, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereDensityRestriction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
namespace Mahler

/-- Pointwise adapted tangent frames suffice; no global tangent frame is
chosen or assumed continuous. -/
theorem exists_outward_tangent_frame {k : ℕ} {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) :
    ∃ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) ∧ sphereVolume k (Matrix.vecCons x v) = 1 := by
  obtain ⟨L,hL⟩ := exists_unitary_referencePole hx
  refine ⟨L ∘ poleFrameFin k, ?_, ?_⟩
  · intro i
    rw [← hL]
    exact (unitary_real_inner L _ _).trans
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (poleFrameVector_tangent _))
  · have he : Matrix.vecCons x (L ∘ poleFrameFin k) =
        L ∘ Matrix.vecCons (referencePole k) (poleFrameFin k) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simpa [Matrix.vecCons] using hL.symm
    rw [he, sphereVolume_unitary, poleFrameFin_volume]

/-- The ambient cofactor formula depends only on the actual tangent
restriction of the boundary form. -/
theorem orientedDensity_congr_on_tangent {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1)
    {B C : ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ}
    (h : ∀ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) → B v = C v) :
    orientedDensity (sphereFrame k) (sphereVolume k) B x =
      orientedDensity (sphereFrame k) (sphereVolume k) C x := by
  obtain ⟨v,hv,hvol⟩ := exists_outward_tangent_frame hx
  have hB := orientedDensity_spec (sphereFrame k) (sphereVolume k)
    (sphereVolume_frame_ne_zero k) B hx v hv
  have hC := orientedDensity_spec (sphereFrame k) (sphereVolume k)
    (sphereVolume_frame_ne_zero k) C hx v hv
  rw [hvol, mul_one] at hB hC
  rw [← hB, ← hC, h v hv]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousSmoothForms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The required local smoothness follows from the literal holomorphic data,
for every finite order, wherever tau is positive. -/
lemma contDiffAt_logTau_order [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (q : ℕ) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    ContDiffAt ℝ q (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ q (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU q (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ q (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := q) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma contDiffAt_dcLinear_order {u : E → ℂ} {x : E} (q : ℕ)
    (hu : ContDiffAt ℝ (q+1) u x) : ContDiffAt ℝ q (dcLinear u) x := by
  have hd : ContDiffAt ℝ q (fderiv ℝ u) x := hu.fderiv_right (by norm_cast)
  exact (hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_oneForm_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E} (q : ℕ)
    (ha : ContDiffAt ℝ q a x) : ContDiffAt ℝ q (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp x ha

theorem MassHypotheses.alpha_beta_contDiffAt {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (alphaPath (polynomialMap G) (coordinateMap n) m t) z ∧
    ContDiffAt ℝ q (betaLinear (polynomialMap G) (coordinateMap n) m) z := by
  have hg := contDiffAt_dcLinear_order q (contDiffAt_logTau_order (q+1)
    isOpen_univ (Set.mem_univ z)
    (fun j => (polynomialMap_differentiable G j).differentiableOn)
    (tau_pos_of_component_ne_zero (h.leading_nonzero z hz)))
  have h0 := contDiffAt_dcLinear_order q (contDiffAt_logTau_order (q+1)
    isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn)
    (coordinateMap_tau_pos hz))
  have hb := hg.sub (h0.const_smul (m : ℝ))
  exact ⟨(h0.const_smul (m : ℝ)).add (hb.const_smul t), hb⟩

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PrimitiveRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped TensorProduct

noncomputable section
namespace Mahler
variable {E X J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma contDiffAt_bundleFiniteForm (b : Module.Basis J ℝ E)
    {a : X → E [⋀^ι]→ₗ[ℝ] ℂ} {x : X} (s : ℕ)
    (ha : ∀ v, ContDiffAt ℝ s (fun y => a y v) x) :
    ContDiffAt ℝ s (fun y => bundleFiniteForm b (a y)) x := by
  apply ContDiffAt.sum
  intro q hq
  exact ((ha _).div_const _).smul contDiffAt_const

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_wedge_eval [FiniteDimensional ℝ E] {a : X → E [⋀^ι]→ₗ[ℝ] ℂ}
    {b : X → E [⋀^κ]→ₗ[ℝ] ℂ} {x : X} (s : ℕ)
    (ha : ∀ v, ContDiffAt ℝ s (fun y => a y v) x)
    (hb : ∀ v, ContDiffAt ℝ s (fun y => b y v) x) (v : ι ⊕ κ → E) :
    ContDiffAt ℝ s (fun y => wedge (a y) (b y) v) x := by
  have ht (σ : Equiv.Perm.ModSumCongr ι κ) :
      ContDiffAt ℝ s (fun y => (LinearMap.mul' ℝ ℂ)
        (AlternatingMap.domCoprod.summand (a y) (b y) σ v)) x := by
    induction σ using Quotient.inductionOn' with
    | h σ =>
      simp only [wedge_summand_eval]
      exact contDiffAt_const.mul ((ha _).mul (hb _))
  simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    _root_.sum_apply, _root_.map_sum] using
    (ContDiffAt.sum (s := Finset.univ) (fun σ _ => ht σ))

lemma contDiffAt_wedgePower_eval {a : X → E [⋀^Fin 2]→ₗ[ℝ] ℂ}
    {x : X} (s : ℕ) (ha : ∀ v, ContDiffAt ℝ s (fun y => a y v) x)
    (k : ℕ) (v : WedgePowerSlots k → E) :
    ContDiffAt ℝ s (fun y => wedgePower (a y) k v) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih => exact contDiffAt_wedge_eval s ha ih v

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousPrimitiveRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set

noncomputable section
namespace Mahler

/-- Evaluation at a fixed tuple preserves finite-order regularity. -/
lemma contDiffAt_form_eval {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {x : X} (q : ℕ)
    (ha : ContDiffAt ℝ q a x) (v : ι → E) :
    ContDiffAt ℝ q (fun y => a y v) x := by
  let ev : (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    { toFun := fun A => A v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_eval_const v }
  exact ev.contDiff.contDiffAt.comp x ha

lemma contDiffAt_extDeriv_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {a : E → E [⋀^Fin p]→L[ℝ] ℂ} {x : E} (q : ℕ)
    (ha : ContDiffAt ℝ (q+1) a x) :
    ContDiffAt ℝ q (extDeriv a) x := by
  have hd : ContDiffAt ℝ q (fderiv ℝ a) x := ha.fderiv_right (by norm_cast)
  exact (alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x hd

theorem MassHypotheses.sourceHomogeneousPrimitive_contDiffAt {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (sourceHomogeneousPrimitive (m := m) G t) x := by
  apply contDiffAt_bundleFiniteForm
  intro v
  have hs := h.alpha_beta_contDiffAt hx t q
  have hs1 := h.alpha_beta_contDiffAt hx t (q+1)
  apply contDiffAt_wedge_eval q
  · intro w
    exact contDiffAt_form_eval q (contDiffAt_oneForm_order q hs.1) w
  · apply contDiffAt_wedge_eval q
    · intro w
      exact contDiffAt_form_eval q (contDiffAt_oneForm_order q hs.2) w
    · apply contDiffAt_wedgePower_eval q
      intro w
      exact contDiffAt_form_eval q (contDiffAt_extDeriv_order q
        (contDiffAt_oneForm_order (q+1) hs1.1)) w

theorem MassHypotheses.sourceHomogeneousPrimitive_C2 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ) : ContDiffOn ℝ 2 (sourceHomogeneousPrimitive (m := m) G t) ({0}ᶜ) := by
  intro x hx
  exact (h.sourceHomogeneousPrimitive_contDiffAt (by simpa using hx) t 2).contDiffWithinAt

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourcePrimitiveStokes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set Metric MeasureTheory

noncomputable section
namespace Mahler

/-- A form agreeing pointwise on sphere tangent tuples with a fixed real scalar
multiple of an exact form has zero sphere flux. -/
theorem sphereFlux_eq_zero_of_tangent_exact_C2 {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ)
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k)]→L[ℝ] ℂ)
    (c : ℝ) (hreg : ContDiffOn ℝ 2 eta ({0}ᶜ))
    (he : ∀ x, ‖x‖ = 1 → ∀ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) → B x v = (c : ℂ) * extDeriv eta x v) :
    sphereFlux k B = 0 := by
  have hz : sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) = 0 := by
    apply sphereFlux_extDeriv_eq_zero_of_C2 _ isOpen_compl_singleton _ hreg
    intro x hx
    have hn : ‖x‖ = 1 := by simpa using hx
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show x ≠ 0 from by intro he; simp [he] at hn)
  have hi : sphereFlux k B = c * sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) := by
    unfold sphereFlux
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    have hx : ‖(x : ComplexEuclidean (k+1))‖ = 1 := by simp
    have hd := orientedDensity_congr_on_tangent hx
      (B := B x) (C := (c : ℂ) • (extDeriv eta x).toAlternatingMap)
      (fun v hv => he x hx v hv)
    rw [hd, orientedDensity_smul]
    simp
  rw [hi, hz, mul_zero]

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousTransgressionFTC
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric
open scoped Topology

noncomputable section
namespace Mahler

theorem MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq_oai {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ)
    (ht : ∀ x : ComplexEuclidean (k+2), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v) :
    sphereFlux (k+1) (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m)) = 0 := by
  apply sphereFlux_eq_zero_of_tangent_exact_C2 _
    (sourceHomogeneousPrimitive (m := m) G t) (-((k+1 : ℕ) : ℝ))
    (h.sourceHomogeneousPrimitive_C2 t)
  simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using ht

end Mahler

end

end OAI
end

theorem solution : type_of% @OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq_oai := @OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq_oai
