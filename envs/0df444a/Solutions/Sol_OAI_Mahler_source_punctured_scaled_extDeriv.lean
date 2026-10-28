-- Prove2me | solution 1 for OAI.Mahler.source_punctured_scaled_extDeriv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:48:16.091417+00:00
-- url     : https://prove2.me/submissions/7370fff9-e638-47f0-be7d-5a59670a2335

import Mathlib
import Definitions.Def_OAISMh000

section
-- module Solutions.OAIS_Mahler.Compat
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CoordinateBall
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_CoordinateAnnulus
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_ShellRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_FormStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_ChartStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma contDiff_orientedCoefficient {n : ℕ}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω) (i : Fin (n+1)) : ContDiff ℝ 1 (orientedCoefficient ω i) := by
  have h := (((-1 : ℝ)^i.val • ContinuousAlternatingMap.apply ℝ _ ℝ
    (i.removeNth (coordinateBasis (n+1)))).contDiff.comp hω)
  change ContDiff ℝ 1 (fun x => (-1 : ℝ)^i.val * ω x (i.removeNth (coordinateBasis (n+1))))
  simpa only [Function.comp_def, smul_apply, smul_eq_mul, ContinuousAlternatingMap.apply_apply] using h

lemma extDeriv_eq_divergence {n : ℕ}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    {x : Fin (n+1) → ℝ} (hω : DifferentiableAt ℝ ω x) :
    extDeriv ω x (coordinateBasis (n+1)) =
      ∑ i : Fin (n+1), fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1) := by
  rw [extDeriv_apply hω]
  apply Finset.sum_congr rfl
  intro i _
  have hd := (hω.continuousAlternatingMap_apply_const
    (i.removeNth (coordinateBasis (n+1)))).hasFDerivAt.const_mul ((-1 : ℝ)^i.val)
  change HasFDerivAt (orientedCoefficient ω i) _ x at hd
  rw [hd.fderiv]
  simp [coordinateBasis, zsmul_eq_mul]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularLevelCharts
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

lemma exists_nonzero_coordinate {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ k : Fin d, L (Pi.single k 1) ≠ 0 := by
  classical
  by_contra! h
  apply hL
  ext x
  have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [h]

lemma hasFDerivAt_levelCoordinates {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {L : (Fin d → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L x) (k : Fin d) :
    HasFDerivAt (levelCoordinates g k) (levelDerivative L k) x := by
  classical
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = k
  · subst i; simpa [levelCoordinates, levelDerivative] using hg
  · simpa [levelCoordinates, levelDerivative, hi] using (hasFDerivAt_apply i x)

lemma contDiffAt_levelCoordinates {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {r : WithTop ℕ∞} (hg : ContDiffAt ℝ r g x) (k : Fin d) :
    ContDiffAt ℝ r (levelCoordinates g k) x := by
  classical
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i = k
  · subst i; simpa [levelCoordinates] using hg
  · simpa [levelCoordinates, hi] using (contDiffAt_apply ℝ ℝ i (f := x))

/-- A genuine C2 chart flattening a regular level. No boundary decomposition is assumed. -/
theorem exists_regular_level_chart {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hg : ContDiffAt ℝ 2 g x) (hreg : fderiv ℝ g x ≠ 0) :
    ∃ (k : Fin d) (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)),
      x ∈ e.source ∧ (∀ z, e z = levelCoordinates g k z) ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target := by
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate (fderiv ℝ g x) hreg
  let L := levelDerivativeEquiv (fderiv ℝ g x) k hk
  have hd : HasFDerivAt (levelCoordinates g k) (L : _ →L[ℝ] _) x :=
    hasFDerivAt_levelCoordinates (hg.differentiableAt (by simp)).hasFDerivAt k
  have hc := contDiffAt_levelCoordinates hg k
  let e := hc.toOpenPartialHomeomorph (levelCoordinates g k) hd (by simp)
  have hx : x ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he : (e : (Fin d → ℝ) → (Fin d → ℝ)) = levelCoordinates g k :=
    hc.toOpenPartialHomeomorph_coe hd (by simp)
  have hi : ContDiffAt ℝ 2 e.symm (e x) := by
    apply e.contDiffAt_symm (f₀' := L) (e.map_source hx)
    · rw [e.left_inv hx, he]
      exact hd
    · rw [e.left_inv hx, he]
      exact hc
  refine ⟨k, e.restrContDiff ℝ 2 (by simp), ?_, ?_, ?_, ?_⟩
  · exact ⟨hx, hc, hi⟩
  · intro z; rfl
  · exact e.contDiffOn_restrContDiff_source ℝ (by simp)
  · exact e.contDiffOn_restrContDiff_target ℝ (by simp)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularSublevel
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

lemma isOpen_regularSublevel {d : ℕ} {U : Set (Fin d → ℝ)} {g : (Fin d → ℝ) → ℝ}
    {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U) : IsOpen (regularSublevel U g R) := by
  exact hg.isOpen_inter_preimage hU isOpen_Iio

/-- Regularity forces a point on the level to be approached from below:
otherwise it would be a local minimum with zero derivative. -/
theorem level_mem_closure_sublevel {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} {x : Fin d → ℝ}
    (hU : IsOpen U) (hx : x ∈ U) (heq : g x = R) (hreg : fderiv ℝ g x ≠ 0) :
    x ∈ closure (regularSublevel U g R) := by
  by_contra hc
  have hm : IsLocalMin g x := by
    filter_upwards [hU.mem_nhds hx, isClosed_closure.isOpen_compl.mem_nhds hc] with y hy hyn
    rw [heq]
    by_contra! hn
    exact hyn (subset_closure ⟨hy, hn⟩)
  exact hreg hm.fderiv_eq_zero

/-- The boundary of the actual relatively defined sublevel is exactly the
regular level, provided its closure stays inside U. -/
theorem frontier_regularSublevel {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0) :
    frontier (regularSublevel U g R) = U ∩ {x | g x = R} := by
  have ho := isOpen_regularSublevel (R := R) hU hg
  rw [ho.frontier_eq]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    have hxU := hcl hx
    refine ⟨hxU, le_antisymm ?_ ?_⟩
    · by_contra! hlt
      have hn : ∀ᶠ y in 𝓝 x, R < g y :=
        (hg.continuousAt (hU.mem_nhds hxU)).preimage_mem_nhds (isOpen_Ioi.mem_nhds hlt)
      obtain ⟨y, hy, hys⟩ := mem_closure_iff_nhds.mp hx {y | R < g y} hn
      exact (not_lt_of_ge (le_of_lt (show R < g y from hy))) (show g y < R from hys.2)
    · exact le_of_not_gt (fun h => hnot ⟨hxU, h⟩)
  · rintro ⟨hxU, heq⟩
    exact ⟨level_mem_closure_sublevel hU hxU heq (hreg x hxU heq),
      fun h => (ne_of_lt h.2) heq⟩

 theorem isCompact_regularLevel {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0) :
    IsCompact (U ∩ {x | g x = R}) := by
  rw [← frontier_regularSublevel hU hg hcl hreg]
  exact hc.of_isClosed_subset isClosed_frontier frontier_subset_closure

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularBoundaryAtlas
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

 theorem exists_regularBoundaryPatch {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hg : ContDiffAt ℝ 2 g x) (hreg : fderiv ℝ g x ≠ 0) :
    ∃ p : RegularBoundaryPatch d U g, x ∈ p.domain := by
  obtain ⟨k, e, he, heq, hs, hi⟩ := exists_regular_level_chart hg hreg
  refine ⟨⟨k, e, e.source ∩ U ∩ Metric.ball x 1,
    (e.open_source.inter hU).inter Metric.isOpen_ball,
    (Metric.isBounded_ball).subset inter_subset_right,
    fun z hz => hz.1.1, fun z hz => hz.1.2, heq, hs, hi⟩, ?_⟩
  exact ⟨⟨he, hx⟩, Metric.mem_ball_self (by norm_num)⟩

attribute [instance] RegularBoundaryAtlas.finite

 theorem exists_regularBoundaryAtlas {d : ℕ} {U K : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ∀ x ∈ K, ContDiffAt ℝ 2 g x)
    (hreg : ∀ x ∈ K, fderiv ℝ g x ≠ 0) :
    Nonempty (RegularBoundaryAtlas d U g K) := by
  classical
  have hp (x : K) := exists_regularBoundaryPatch hU (hKU x.property)
    (hg x x.property) (hreg x x.property)
  choose p hp using hp
  have hcover : K ⊆ ⋃ x : K, (p x).domain := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hp ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => (p x).domain)
    (fun x => (p x).open_domain) hcover
  refine ⟨⟨t, inferInstance, fun i => p i.val, ?_⟩⟩
  intro x hx
  obtain ⟨i, hit, hi⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion.mpr ⟨⟨i, hit⟩, hi⟩

/-- The chart identifies the actual sublevel with the lower coordinate half-space. -/
theorem RegularBoundaryPatch.sublevel_iff {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} (p : RegularBoundaryPatch d U g) {R : ℝ}
    {x : Fin d → ℝ} (hx : x ∈ p.domain) :
    x ∈ regularSublevel U g R ↔ p.chart x p.coordinate < R := by
  rw [p.chart_eq]
  simp [levelCoordinates, regularSublevel, p.domain_U hx]

 theorem exists_sublevelBoundaryAtlas {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0) :
    Nonempty (RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) := by
  rw [frontier_regularSublevel hU hg.continuousOn hcl hreg]
  exact exists_regularBoundaryAtlas hU
    (isCompact_regularLevel hU hg.continuousOn hc hcl hreg) inter_subset_left
    (fun x hx => hg.contDiffAt (hU.mem_nhds hx.1)) (fun x hx => hreg x hx.1 hx.2)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularPartition
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology Manifold
namespace MahlerStokes

/-- An actual smooth partition with compact supports in a given finite bounded
open cover, equal to one on a neighborhood of the compact set. -/
theorem exists_compact_smooth_partition {d : ℕ} {ι : Type} [Fintype ι]
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (V : ι → Set (Fin d → ℝ))
    (hVo : ∀ i, IsOpen (V i)) (hVb : ∀ i, Bornology.IsBounded (V i))
    (hcover : K ⊆ ⋃ i, V i) :
    ∃ (W : Set (Fin d → ℝ))
      (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) (closure W)),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧
      ρ.IsSubordinate V ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_iUnion hVo) hcover
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Fin d → ℝ) isClosed_closure V hVo hWV
  refine ⟨W, ρ, hWo, hKW, hWc, hρ, ?_, ?_⟩
  · intro i
    exact Metric.isCompact_of_isClosed_isBounded isClosed_closure ((hVb i).subset (hρ i))
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_closure hx)

 theorem sublevelPatchDomain_covers {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (a : RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) :
    closure (regularSublevel U g R) ⊆ ⋃ i, sublevelPatchDomain a i := by
  intro x hx
  by_cases hi : x ∈ regularSublevel U g R
  · exact mem_iUnion.mpr ⟨none, hi⟩
  · have hf : x ∈ frontier (regularSublevel U g R) := by
      rw [(isOpen_regularSublevel hU hg).frontier_eq]
      exact ⟨hx, hi⟩
    obtain ⟨i, hix⟩ := mem_iUnion.mp (a.covers hf)
    exact mem_iUnion.mpr ⟨some i, hix⟩

 theorem exists_sublevel_partition {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (a : RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) :
    ∃ (W : Set (Fin d → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel U g R) ⊆ W ∧ IsCompact (closure W) ∧
      ρ.IsSubordinate (sublevelPatchDomain a) ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) := by
  apply exists_compact_smooth_partition hc (sublevelPatchDomain a)
  · intro i
    cases i with
    | none => exact isOpen_regularSublevel hU hg
    | some i => exact (a.patch i).open_domain
  · intro i
    cases i with
    | none => exact hc.isBounded.subset subset_closure
    | some i => exact (a.patch i).bounded_domain
  · exact sublevelPatchDomain_covers hU hg a

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FormLocalization
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem extDeriv_finsetSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {ι : Type*} (t : Finset ι)
    (ω : ι → E → E [⋀^Fin n]→L[ℝ] ℝ) (x : E)
    (hω : ∀ i ∈ t, DifferentiableAt ℝ (ω i) x) :
    extDeriv (fun z => ∑ i ∈ t, ω i z) x = ∑ i ∈ t, extDeriv (ω i) x := by
  simp only [extDeriv, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    fderiv_fun_sum hω, map_sum]

/-- The cutoff derivatives cancel because the actual localized forms sum to
ω on a neighborhood; no boundary or Stokes equation is assumed. -/
theorem extDeriv_partition_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {ι : Type*} [Fintype ι] {W : Set E} {x : E}
    (ρ : ι → E → ℝ) (ω : E → E [⋀^Fin n]→L[ℝ] ℝ)
    (hW : IsOpen W) (hx : x ∈ W) (hsum : ∀ z ∈ W, ∑ i, ρ i z = 1)
    (hω : ∀ i, DifferentiableAt ℝ (fun z => ρ i z • ω z) x) :
    extDeriv ω x = ∑ i, extDeriv (fun z => ρ i z • ω z) x := by
  have he : ω =ᶠ[𝓝 x] (fun z => ∑ i, ρ i z • ω z) := by
    filter_upwards [hW.mem_nhds hx] with z hz
    rw [← Finset.sum_smul, hsum z hz, one_smul]
  rw [he.extDeriv_eq]
  exact extDeriv_finsetSum Finset.univ _ x (fun i _ => hω i)

 theorem contDiff_localized_form {d n : ℕ} {ι : Type*} {K : Set (Fin d → ℝ)}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) K)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i : ι)
    (hω : ∀ x ∈ tsupport (ρ i), ContDiffAt ℝ 1 ω x) :
    ContDiff ℝ 1 (fun x => ρ i x • ω x) := by
  exact (ρ.contMDiff_smul (fun x hx => (hω x hx).contMDiffAt)).contDiff

 theorem hasCompactSupport_localized_form {d n : ℕ} {ι : Type*}
    (ρ : ι → (Fin d → ℝ) → ℝ)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i : ι)
    (hρ : HasCompactSupport (ρ i)) : HasCompactSupport (fun x => ρ i x • ω x) := by
  exact hρ.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)

/-- Every localized C1 compactly supported form has an integrable actual
exterior-derivative coefficient on the whole coordinate space. -/
theorem integrable_extDeriv_coefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    Integrable (fun x => extDeriv ω x (coordinateBasis (n+1))) := by
  have hi (i : Fin (n+1)) : Integrable
      (fun x => fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) := by
    have hs : HasCompactSupport (orientedCoefficient ω i) :=
      hc.comp_left (g := fun A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ => (-1 : ℝ)^i.val *
        A (i.removeNth (coordinateBasis (n+1)))) (by simp)
    exact (((contDiff_orientedCoefficient hω i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ (Pi.single i 1))
  have he (x) := extDeriv_eq_divergence (hω.differentiable one_ne_zero x)
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => hi i)

/-- Actual volume integral localization for a finite smooth partition, on
any measurable set contained in its sum-one neighborhood. -/
theorem integral_extDeriv_partition {n : ℕ} {ι : Type*} [Fintype ι]
    {K W s : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin (n+1) → ℝ) (Fin (n+1) → ℝ) K)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hW : IsOpen W) (hsW : s ⊆ W) (hs : MeasurableSet s)
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (hρ : ∀ i, HasCompactSupport (ρ i))
    (hω : ∀ i, ∀ x ∈ tsupport (ρ i), ContDiffAt ℝ 1 ω x) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i, ∫ x in s, extDeriv (fun z => ρ i z • ω z) x (coordinateBasis (n+1)) := by
  have hd (i) := contDiff_localized_form ρ ω i (hω i)
  have hi (i) := integrable_extDeriv_coefficient _ (hd i)
    (hasCompactSupport_localized_form (fun i x => ρ i x) ω i (hρ i))
  calc
    _ = ∫ x in s, ∑ i, extDeriv (fun z => ρ i z • ω z) x (coordinateBasis (n+1)) := by
      apply setIntegral_congr_fun hs
      intro x hx
      dsimp only
      rw [extDeriv_partition_sum (fun i x => ρ i x) ω hW (hsW hx) hsum
        (fun i => (hd i).differentiable one_ne_zero x)]
      simp
    _ = _ := integral_finsetSum _ (fun i _ => (hi i).integrableOn)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HalfspaceStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

lemma measurableSet_lowerHalfspace {d : ℕ} (k : Fin d) (R : ℝ) :
    MeasurableSet (lowerHalfspace k R) :=
  (isOpen_lt (continuous_apply k) continuous_const).measurableSet

lemma slice_eq_update {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    (fun t : ℝ => (i.insertNth t y : Fin (n+1) → ℝ)) =
      Function.update (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) i := by
  funext t
  exact (Fin.update_insertNth (α := fun _ : Fin (n+1) => ℝ) i 0 t y).symm

lemma contDiff_slice {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => (i.insertNth t y : Fin (n+1) → ℝ)) := by
  rw [slice_eq_update]
  exact contDiff_update 1 _ _

lemma hasCompactSupport_slice {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun t => f (i.insertNth t y)) := by
  change HasCompactSupport (f ∘ (fun t => i.insertNth t y))
  rw [slice_eq_update]
  exact hf.comp_isClosedEmbedding (isClosedEmbedding_update _ _)

lemma integral_partial_slice_Iio {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (R : ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ t in Iio R, fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) = f (i.insertNth R y) := by
  have hd (t : ℝ) := ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)).deriv
  have hs := hf.comp (contDiff_slice i y)
  have hsc := hasCompactSupport_slice i y hc
  have h := HasCompactSupport.integral_Iic_deriv_eq hs hsc R
  rw [integral_Iic_eq_integral_Iio] at h
  change ∀ t, deriv (fun s => f (i.insertNth s y)) t = _ at hd
  change (∫ t in Iio R, deriv (fun s => f (i.insertNth s y)) t) = _ at h
  simpa only [hd, Function.comp_def] using h

lemma integral_partial_slice_zero {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ t, fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) = 0 := by
  have hs : ContDiff ℝ 1 (fun t => f (i.insertNth t y)) := hf.comp (contDiff_slice i y)
  have hsc := hasCompactSupport_slice i y hc
  have hd (t : ℝ) := (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)
  have he (t : ℝ) := (hd t).deriv
  apply integral_eq_zero_of_hasDerivAt_of_integrable hd
  · have hi : Integrable (deriv (fun t => f (i.insertNth t y))) :=
      hs.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hsc.deriv
    change ∀ t, deriv (fun s => f (i.insertNth s y)) t = _ at he
    change Integrable (fun t => deriv (fun s => f (i.insertNth s y)) t) at hi
    simpa only [he] using hi
  · exact hs.continuous.integrable_of_hasCompactSupport hsc

/-- Coordinate divergence through a flat boundary. Transverse derivatives
integrate to zero; the k derivative gives the upper face with positive sign. -/
theorem integral_partial_lowerHalfspace {n : ℕ} (i k : Fin (n+1)) (R : ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ x in lowerHalfspace k R, fderiv ℝ f x (Pi.single i 1)) =
      if i = k then ∫ y : Fin n → ℝ, f (k.insertNth R y) else 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (Pi.single i 1))
  rw [setIntegral_slice i (measurableSet_lowerHalfspace k R) _ hi.integrableOn]
  by_cases hik : i = k
  · subst i
    simp only [↓reduceIte]
    have hslice (y : Fin n → ℝ) :
        {t : ℝ | k.insertNth t y ∈ lowerHalfspace k R} = Iio R := by
      ext t
      simp [lowerHalfspace]
    simp_rw [hslice, integral_partial_slice_Iio k _ R hf hc]
  · rw [ite_eq_right hik]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    have he (t : ℝ) : (i.insertNth t y : Fin (n+1) → ℝ) k = (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) k := by
      rw [← Fin.update_insertNth (α := fun _ : Fin (n+1) => ℝ) i 0 t y]
      simp [Ne.symm hik]
    by_cases hy : (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) k < R
    · have hslice : {t : ℝ | i.insertNth t y ∈ lowerHalfspace k R} = univ := by
        ext t
        simp [lowerHalfspace, he, hy]
      rw [hslice, setIntegral_univ]
      exact integral_partial_slice_zero i y hf hc
    · have hslice : {t : ℝ | i.insertNth t y ∈ lowerHalfspace k R} = ∅ := by
        ext t
        simp [lowerHalfspace, he, hy]
      simp [hslice]

/-- Stokes on a coordinate half-space for an actual compactly supported C1
form. The boundary uses the outward orientation, including (-1)^k. -/
theorem integral_extDeriv_lowerHalfspace {n : ℕ} (k : Fin (n+1)) (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    (∫ x in lowerHalfspace k R, extDeriv ω x (coordinateBasis (n+1))) =
      (-1 : ℝ)^k.val * ∫ y : Fin n → ℝ,
        ω (k.insertNth R y) (k.removeNth (coordinateBasis (n+1))) := by
  have hs (i : Fin (n+1)) : HasCompactSupport (orientedCoefficient ω i) :=
    hc.comp_left (g := fun A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ =>
      (-1 : ℝ)^i.val * A (i.removeNth (coordinateBasis (n+1)))) (by simp)
  have hi (i : Fin (n+1)) : Integrable
      (fun x => fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) :=
    (((contDiff_orientedCoefficient hω i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hs i).fderiv_apply ℝ (Pi.single i 1))
  simp_rw [extDeriv_eq_divergence (hω.differentiable one_ne_zero _)]
  rw [integral_finsetSum _ (fun i _ => (hi i).integrableOn)]
  simp_rw [integral_partial_lowerHalfspace _ k R (contDiff_orientedCoefficient hω _) (hs _)]
  simp [orientedCoefficient, integral_const_mul]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_InteriorStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem extDeriv_zero_off_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) {x : E} (hx : x ∉ tsupport ω) :
    extDeriv ω x = 0 := by
  rw [extDeriv, fderiv_of_notMem_tsupport ℝ hx]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)

 theorem integral_partial_univ {n : ℕ} (i : Fin (n+1))
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ x, fderiv ℝ f x (Pi.single i 1)) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (Pi.single i 1))
  rw [← setIntegral_univ, setIntegral_slice i MeasurableSet.univ _ hi.integrableOn]
  simp only [mem_univ, ofPred_true, setIntegral_univ]
  simp_rw [integral_partial_slice_zero i _ hf hc]
  simp

/-- Stokes for a compactly supported form in the whole ambient space. -/
theorem integral_extDeriv_univ {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    (∫ x, extDeriv ω x (coordinateBasis (n+1))) = 0 := by
  have hs (i : Fin (n+1)) : HasCompactSupport (orientedCoefficient ω i) :=
    hc.comp_left (g := fun A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ =>
      (-1 : ℝ)^i.val * A (i.removeNth (coordinateBasis (n+1)))) (by simp)
  have hi (i : Fin (n+1)) : Integrable
      (fun x => fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) :=
    (((contDiff_orientedCoefficient hω i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hs i).fderiv_apply ℝ (Pi.single i 1))
  simp_rw [extDeriv_eq_divergence (hω.differentiable one_ne_zero _)]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_partial_univ _ (contDiff_orientedCoefficient hω _) (hs _)]
  simp

/-- The actual interior patch contributes zero, since the support of the
localized form stays strictly inside the domain. -/
theorem integral_extDeriv_interior_support {n : ℕ} {s : Set (Fin (n+1) → ℝ)}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ s) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_extDeriv_univ ω hω hc
  · intro x hx
    rw [extDeriv_zero_off_tsupport ω (fun h => hx (hs h))]
    simp

/-- Remove the interior term from the volume partition. All remaining
terms are supported in boundary charts, before oriented chart transport. -/
theorem integral_extDeriv_boundary_patches {n : ℕ} {ι : Type*} [Fintype ι]
    {K W s : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity (Option ι) 𝓘(ℝ, Fin (n+1) → ℝ) (Fin (n+1) → ℝ) K)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hW : IsOpen W) (hsW : s ⊆ W) (hs : MeasurableSet s)
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (hρ : ∀ i, HasCompactSupport (ρ i))
    (hω : ∀ i, ∀ x ∈ tsupport (ρ i), ContDiffAt ℝ 1 ω x)
    (hinterior : tsupport (ρ none) ⊆ s) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : ι, ∫ x in s,
        extDeriv (fun z => ρ (some i) z • ω z) x (coordinateBasis (n+1)) := by
  rw [integral_extDeriv_partition ρ ω hW hsW hs hsum hρ hω, Fintype.sum_option]
  have hz := integral_extDeriv_interior_support (fun z => ρ none z • ω z)
    (contDiff_localized_form ρ ω none (hω none))
    (hasCompactSupport_localized_form (fun i x => ρ i x) ω none (hρ none))
    ((tsupport_smul_subset_left _ _).trans hinterior)
  rw [hz, zero_add]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OrientedChartIntegral
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

lemma jacobianOrientation_mul (a : ℝ) : jacobianOrientation a * a = |a| := by
  unfold jacobianOrientation
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

/-- A top alternating form transforms by the determinant in the ordered
standard coordinate basis. -/
theorem topForm_apply_linear {d : ℕ}
    (A : (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    A (fun i => L (coordinateBasis d i)) = L.det * A (coordinateBasis d) := by
  let b := Pi.basisFun ℝ (Fin d)
  have he := congrArg (fun f : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ =>
    f (fun i => L (b i))) (A.toAlternatingMap.eq_smul_basis_det b)
  have hd : b.det (fun i => L (b i)) = L.det := by
    change b.det (L.toLinearMap ∘ b) = L.det
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at he
  rw [hd] at he
  have hb : (b : Fin d → (Fin d → ℝ)) = coordinateBasis d := by
    ext i j
    simp [b, coordinateBasis]
  rw [← hb]
  exact he.trans (mul_comm _ _)

/-- Actual Lebesgue change of variables for an oriented top form. The
orientation factor converts the signed determinant to the positive Jacobian. -/
theorem integral_image_topForm {d : ℕ} {s : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) → (Fin d → ℝ))
    (A : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ)
    (hs : MeasurableSet s) (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x) (hinj : InjOn φ s) :
    (∫ x in φ '' s, A x (coordinateBasis d)) =
      ∫ y in s, jacobianOrientation (fderiv ℝ φ y).det *
        A (φ y) (fun i => fderiv ℝ φ y (coordinateBasis d i)) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply integral_congr_ae
  filter_upwards with y
  rw [topForm_apply_linear, ← mul_assoc, jacobianOrientation_mul]
  rfl

/-- At a nonzero Jacobian, orientation is locally constant. -/
theorem jacobianOrientation_eventuallyEq {E : Type*} [TopologicalSpace E]
    {f : E → ℝ} {x : E} (hf : ContinuousAt f x) (hx : f x ≠ 0) :
    (fun y => jacobianOrientation (f y)) =ᶠ[𝓝 x] (fun _ => jacobianOrientation (f x)) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hn : ∀ᶠ y in 𝓝 x, f y < 0 := hf.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hn] with y hy
    simp [jacobianOrientation, not_le.mpr hy, not_le.mpr hneg]
  · have hn : ∀ᶠ y in 𝓝 x, 0 < f y := hf.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hn] with y hy
    simp [jacobianOrientation, hy.le, hpos.le]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PullbackRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

 theorem contDiffAt_of_toMultilinear {d n : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ} {x : X}
    (hf : ContDiffAt ℝ 1 (fun y => (f y).toContinuousMultilinearMap) x) :
    ContDiffAt ℝ 1 f x := by
  let J : ((Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hJ : LinearMap.ker J.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  obtain ⟨Q, hQ⟩ := J.toLinearMap.exists_leftInverse_of_injective hJ
  let : FiniteDimensional ℝ ((Fin d → ℝ) [×n]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear)
      ContinuousMultilinearMap.toMultilinearMap_injective
  let Qc := Q.toContinuousLinearMap
  have he : (fun y => Qc ((f y).toContinuousMultilinearMap)) = f := by
    funext y
    exact congrArg (fun L => L (f y)) hQ
  rw [← he]
  exact Qc.contDiff.contDiffAt.comp x hf

/-- The pullback operation is C1 jointly in the form and the linear map.
It is polynomial in the linear map, so C1 regularity needs no extra premise. -/
theorem contDiffAt_compAlternating {d n : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    {L : X → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {x : X}
    (hf : ContDiffAt ℝ 1 f x) (hL : ContDiffAt ℝ 1 L x) :
    ContDiffAt ℝ 1 (fun y => (f y).compContinuousLinearMap (L y)) x := by
  apply contDiffAt_of_toMultilinear
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n => Fin d → ℝ) (fun _ : Fin n => Fin d → ℝ) ℝ
  have hC : ContDiffAt ℝ 1 (fun y => C (fun _ => L y)) x := by
    exact (ContinuousMultilinearMap.contDiffAt
      (F := ((Fin d → ℝ) [×n]→L[ℝ] ℝ) →L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ)) C).comp x
        (contDiffAt_pi.mpr (fun _ : Fin n => hL))
  let J : ((Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ((Fin d → ℝ) [×n]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hF : ContDiffAt ℝ 1 (fun y => (f y).toContinuousMultilinearMap) x :=
    J.contDiff.contDiffAt.comp x hf
  exact hC.clm_apply hF

/-- A C2 parametrization and C1 ambient form give a C1 actual pullback. -/
theorem contDiffAt_pullbackForm {d n : ℕ}
    {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    {ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ} {x : Fin d → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hω : ContDiffAt ℝ 1 ω (φ x)) :
    ContDiffAt ℝ 1 (pullbackForm φ ω) x := by
  exact contDiffAt_compAlternating (hω.comp x (hφ.of_le (by simp)))
    (hφ.fderiv_right (by norm_num))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ChartExtension
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

 theorem chart_inverse_det_ne_zero {d : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (he : ∀ x ∈ e.source, DifferentiableAt ℝ e x)
    (hi : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) {y : Fin d → ℝ} (hy : y ∈ e.target) :
    (fderiv ℝ e.symm y).det ≠ 0 := by
  have hd := (he (e.symm y) (e.map_target hy)).hasFDerivAt.comp y (hi y hy).hasFDerivAt
  have hf : (fun z => e (e.symm z)) =ᶠ[𝓝 y] (fun z => z) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hm : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ (Fin d → ℝ) :=
    (hd.congr_of_eventuallyEq hf.symm).unique (hasFDerivAt_id y)
  have hdet := congrArg ContinuousLinearMap.det hm
  change LinearMap.det ((fderiv ℝ e (e.symm y)).toLinearMap.comp
    (fderiv ℝ e.symm y).toLinearMap) = LinearMap.det (LinearMap.id :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hz
  change LinearMap.det (fderiv ℝ e.symm y).toLinearMap = 0 at hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

 theorem tsupport_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source) :
    tsupport (extendedChartForm e ω) ⊆ e '' tsupport ω := by
  have hK : IsCompact (e '' tsupport ω) := hc.image_of_continuousOn (e.continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro y hy
  have hne : extendedChartForm e ω y ≠ 0 := hy
  have hyt : y ∈ e.target := by
    by_contra h
    exact hne (by simp [extendedChartForm, h])
  have hω : ω (e.symm y) ≠ 0 := by
    intro h
    apply hne
    have hz : pullbackForm e.symm ω y = 0 := by
      ext v
      simp [pullbackForm, h]
    simp [extendedChartForm, hyt, hz]
  exact ⟨e.symm y, subset_tsupport ω hω, e.right_inv hyt⟩

 theorem hasCompactSupport_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source) :
    HasCompactSupport (extendedChartForm e ω) :=
  (hc.image_of_continuousOn (e.continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_extendedChartForm e ω hc hs)

 theorem extendedChartForm_eventuallyEq {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) {y : Fin d → ℝ}
    (hy : y ∈ e.target) (hi : ContDiffAt ℝ 2 e.symm y)
    (hdet : (fderiv ℝ e.symm y).det ≠ 0) :
    extendedChartForm e ω =ᶠ[𝓝 y]
      (fun z => jacobianOrientation (fderiv ℝ e.symm y).det • pullbackForm e.symm ω z) := by
  have hor := jacobianOrientation_eventuallyEq
    (ContinuousLinearMap.continuous_det.continuousAt.comp (hi.continuousAt_fderiv (by simp))) hdet
  dsimp only [Function.comp_def] at hor
  filter_upwards [e.open_target.mem_nhds hy, hor] with z hz horz
  simp only [extendedChartForm, indicator_of_mem hz, horz]

/-- Compact support inside the chart makes extension by zero C1. This proves
the pullback regularity rather than adding it as a Stokes hypothesis. -/
theorem contDiff_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (he : ContDiffOn ℝ 2 e e.source) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source) :
    ContDiff ℝ 1 (extendedChartForm e ω) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · have hiy := hi.contDiffAt (e.open_target.mem_nhds hy)
    have hdet := chart_inverse_det_ne_zero e
      (fun x hx => (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp))
      (fun x hx => (hi.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)) hy
    have hlocal : ContDiffAt ℝ 1 (fun z => jacobianOrientation (fderiv ℝ e.symm y).det •
        pullbackForm e.symm ω z) y :=
      (contDiffAt_const (c := jacobianOrientation (fderiv ℝ e.symm y).det)).smul
        (contDiffAt_pullbackForm hiy hω.contDiffAt)
    exact hlocal.congr_of_eventuallyEq (extendedChartForm_eventuallyEq e ω hy hiy hdet)
  · have hnot : y ∉ tsupport (extendedChartForm e ω) := by
      intro h
      obtain ⟨x, hx, rfl⟩ := tsupport_extendedChartForm e ω hc hs h
      exact hy (e.map_source (hs hx))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hnot)

/-- On the target, the derivative of the oriented extension is the oriented
pullback of the derivative. The orientation is locally constant. -/
theorem extDeriv_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) {y : Fin d → ℝ}
    (hy : y ∈ e.target) (hi : ContDiffAt ℝ 2 e.symm y)
    (hdet : (fderiv ℝ e.symm y).det ≠ 0) (hω : DifferentiableAt ℝ ω (e.symm y)) :
    extDeriv (extendedChartForm e ω) y =
      jacobianOrientation (fderiv ℝ e.symm y).det •
        (extDeriv ω (e.symm y)).compContinuousLinearMap (fderiv ℝ e.symm y) := by
  rw [(extendedChartForm_eventuallyEq e ω hy hi hdet).extDeriv_eq]
  change extDeriv (jacobianOrientation (fderiv ℝ e.symm y).det • pullbackForm e.symm ω) y = _
  rw [extDeriv_smul]
  unfold pullbackForm
  rw [extDeriv_pullback hω hi (by simp)]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeAlgebra
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedgePower_smul (c : ℂ) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (c • a) k = c ^ k • wedgePower a k := by
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = c ^ 0 * 1
    simp
  | succ k ih =>
    change wedge (c • a) (wedgePower (c • a) k) = c ^ (k + 1) • wedge a (wedgePower a k)
    simp only [ih, wedge_smul_left, wedge_smul_right, smul_smul]
    rw [pow_succ]

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
-- module Solutions.OAIS_Mahler.Mahler_ContinuousWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma contDiffAt_continuousWedge [FiniteDimensional ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : WithTop ℕ∞}
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {b : X → E [⋀^κ]→L[ℝ] ℂ} {x : X}
    (ha : ContDiffAt ℝ r a x) (hb : ContDiffAt ℝ r b x) :
    ContDiffAt ℝ r (fun y => continuousWedge (a y) (b y)) x := by
  let W := continuousWedgeCLM (E := E) (ι := ι) (κ := κ)
  have hw := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r)
    (E := E [⋀^ι]→L[ℝ] ℂ)
    (F := (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ) W
  have hw' := hw.contDiffAt.comp x ha
  exact hw'.clm_apply hb

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CoordinateSphere
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma finite_radiusSq_slice {n : ℕ} (i : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) :
    Set.Finite {t : ℝ | radiusSq (i.insertNth t y) = R^2} := by
  apply (Set.toFinite ({chord R y, -chord R y} : Set ℝ)).subset
  intro t ht
  have hsq : t^2 = R^2 - radiusSq y := by
    change radiusSq (i.insertNth t y) = R^2 at ht
    rw [radiusSq_insertNth] at ht; linarith
  have hc : (chord R y)^2 = R^2 - radiusSq y := Real.sq_sqrt (hsq ▸ sq_nonneg t)
  have he : t = chord R y ∨ t = -chord R y := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hc.symm)
  simpa only [mem_insert_iff, mem_singleton_iff] using he

/-- Coordinate Euclidean spheres have zero Lebesgue measure. -/
theorem volume_coordSphere {n : ℕ} (R : ℝ) :
    volume {x : Fin (n+1) → ℝ | radiusSq x = R^2} = 0 := by
  let s : Set (Fin (n+1) → ℝ) := {x | radiusSq x = R^2}
  have hs : MeasurableSet s := (isClosed_eq (continuous_radiusSq _) continuous_const).measurableSet
  have hsub : s ⊆ coordClosedBall (n+1) R := fun x hx => hx.le
  have hf : IntegrableOn (fun _ : Fin (n+1) → ℝ => (1 : ℝ)) s :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_coordClosedBall (n+1) R)).mono_set hsub
  have hi : (∫ x in s, (1 : ℝ)) = 0 := by
    rw [setIntegral_slice (0 : Fin (n+1)) hs _ hf]
    have hz (y : Fin n → ℝ) :
        (∫ t in {t | (0 : Fin (n+1)).insertNth t y ∈ s}, (1 : ℝ)) = 0 := by
      apply setIntegral_measure_zero
      exact (finite_radiusSq_slice 0 R y).measure_zero volume
    simp_rw [hz]
    simp
  have hfinite : volume s ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_coordClosedBall (n+1) R).measure_ne_top (measure_mono hsub)
  have hr : (volume s).toReal = 0 := by simpa [measureReal_def] using hi
  exact (ENNReal.toReal_eq_zero_iff _).1 hr |>.resolve_right hfinite

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HolomorphicRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_Hessian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

local notation "conj" => starRingEnd ℂ

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

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma diff_conj [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x :=
  Complex.conjCLE.differentiableAt.comp x hf

lemma differentiable_energy {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : DifferentiableAt ℝ (energy f) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj ((hf j).restrictScalars ℝ)).mul ((hf j).restrictScalars ℝ))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

/-- C^2 regularity of log tau follows from first-order holomorphicity. -/
lemma contDiffAt_logTau_of_open [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) : ContDiffAt ℝ 2 (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ 2 (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := 2) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma differentiableAt_dcLinear {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact ((hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)).differentiableAt (by norm_num)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousDeformation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ E] in
lemma tau_continuousAt [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : ContinuousAt (tau f) x := by
  have h := Complex.continuous_re.continuousAt.comp (differentiable_energy hf).continuousAt
  simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularChartStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem setIntegral_extDeriv_congr_support {n : ℕ} {s t : Set (Fin (n+1) → ℝ)}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (he : ∀ x ∈ tsupport ω, x ∈ s ↔ x ∈ t) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) =
      ∫ x in t, extDeriv ω x (coordinateBasis (n+1)) := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport ω
  · by_cases hxs : x ∈ s
    · simp [hxs, (he x hx).mp hxs]
    · have hxt : x ∉ t := fun h => hxs ((he x hx).mpr h)
      simp [hxs, hxt]
  · have hz : extDeriv ω x (coordinateBasis (n+1)) = 0 := by
      rw [extDeriv_zero_off_tsupport ω hx]
      simp
    simp [Set.indicator, hz]

 lemma chart_image_target_inter {d : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)) (H : Set (Fin d → ℝ)) :
    e.symm '' (e.target ∩ H) = e.source ∩ e ⁻¹' H := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyt, hyH⟩, rfl⟩
    refine ⟨e.map_target hyt, ?_⟩
    change e (e.symm y) ∈ H
    rw [e.right_inv hyt]
    exact hyH
  · rintro ⟨hxs, hxH⟩
    exact ⟨e x, ⟨e.map_source hxs, hxH⟩, e.left_inv hxs⟩

/-- Stokes for a localized form in a genuine boundary chart. All pullback
regularity, zero extension, Jacobian and outward signs are derived. -/
theorem integral_extDeriv_chart {n : ℕ} {D : Set (Fin (n+1) → ℝ)}
    (e : OpenPartialHomeomorph (Fin (n+1) → ℝ) (Fin (n+1) → ℝ))
    (k : Fin (n+1)) (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hD : MeasurableSet D) (he : ContDiffOn ℝ 2 e e.source)
    (hi : ContDiffOn ℝ 2 e.symm e.target) (hω : ContDiff ℝ 1 ω)
    (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source)
    (hflat : ∀ x ∈ tsupport ω, x ∈ D ↔ e x k < R) :
    (∫ x in D, extDeriv ω x (coordinateBasis (n+1))) = chartBoundaryFlux e k R ω := by
  let S := e.target ∩ lowerHalfspace k R
  let T := e.symm '' S
  let β := extendedChartForm e ω
  have hHo : IsOpen (lowerHalfspace k R) := isOpen_lt (continuous_apply k) continuous_const
  have hSo : IsOpen S := e.open_target.inter hHo
  have hTo : IsOpen T := by
    rw [show T = e.source ∩ e ⁻¹' lowerHalfspace k R from chart_image_target_inter e _]
    exact e.continuousOn.isOpen_inter_preimage e.open_source hHo
  have hβs : tsupport β ⊆ e.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_extendedChartForm e ω hc hs hy
    exact e.map_source (hs hx)
  have hdet (y) (hy : y ∈ e.target) := chart_inverse_det_ne_zero e
    (fun x hx => (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp))
    (fun x hx => (hi.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)) hy
  calc
    _ = ∫ x in T, extDeriv ω x (coordinateBasis (n+1)) := by
      apply setIntegral_extDeriv_congr_support ω hD hTo.measurableSet
      intro x hx
      rw [show T = e.source ∩ e ⁻¹' lowerHalfspace k R from chart_image_target_inter e _]
      simpa only [mem_inter_iff, mem_preimage, lowerHalfspace, mem_ofPred_eq, hs hx, true_and]
        using hflat x hx
    _ = ∫ y in S, jacobianOrientation (fderiv ℝ e.symm y).det *
        extDeriv ω (e.symm y) (fun i => fderiv ℝ e.symm y (coordinateBasis (n+1) i)) :=
      integral_image_topForm e.symm (extDeriv ω) hSo.measurableSet
        (fun y hy => (hi.contDiffAt (e.open_target.mem_nhds hy.1)).differentiableAt (by simp))
        (e.symm.injOn.mono inter_subset_left)
    _ = ∫ y in S, extDeriv β y (coordinateBasis (n+1)) := by
      apply setIntegral_congr_fun hSo.measurableSet
      intro y hy
      dsimp only
      rw [show extDeriv β y = _ from extDeriv_extendedChartForm e ω hy.1
        (hi.contDiffAt (e.open_target.mem_nhds hy.1)) (hdet y hy.1)
        (hω.differentiable one_ne_zero _)]
      rfl
    _ = ∫ y in lowerHalfspace k R, extDeriv β y (coordinateBasis (n+1)) :=
      setIntegral_extDeriv_congr_support β hSo.measurableSet hHo.measurableSet
        (fun y hy => ⟨fun h => h.2, fun h => ⟨hβs hy, h⟩⟩)
    _ = _ := integral_extDeriv_lowerHalfspace k R β
      (contDiff_extendedChartForm e ω he hi hω hc hs)
      (hasCompactSupport_extendedChartForm e ω hc hs)

/-- Stokes with a fixed admissible atlas and partition. The same boundary
representation can therefore be used for two different forms. -/
theorem integral_extDeriv_regular_partition {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R : ℝ}
    (hU : IsOpen U) (hg : ContinuousOn g U)
    (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
    {W : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
      (Fin (n+1) → ℝ) (closure W))
    (hWo : IsOpen W) (hCW : closure (regularSublevel U g R) ⊆ W)
    (hρc : ∀ i, HasCompactSupport (ρ i)) (hρsub : ρ.IsSubordinate (sublevelPatchDomain a))
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω U) :
    (∫ x in regularSublevel U g R, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
        (fun z => ρ (some i) z • ω z) := by
  have hρU (i : Option a.Index) : tsupport (ρ i) ⊆ U := by
    apply (hρsub i).trans
    cases i with
    | none => exact inter_subset_left
    | some i => exact (a.patch i).domain_U
  have hvolume := integral_extDeriv_boundary_patches ρ ω hWo (subset_closure.trans hCW)
    (isOpen_regularSublevel hU hg).measurableSet hsum hρc
    (fun i x hx => hω.contDiffAt (hU.mem_nhds (hρU i hx))) (hρsub none)
  apply hvolume.trans
  apply Finset.sum_congr rfl
  intro i _
  have hsi : tsupport (fun z => ρ (some i) z • ω z) ⊆ (a.patch i).domain :=
    (tsupport_smul_subset_left _ _).trans (hρsub (some i))
  exact integral_extDeriv_chart (a.patch i).chart (a.patch i).coordinate R _
    (isOpen_regularSublevel hU hg).measurableSet
    (a.patch i).smooth_chart (a.patch i).smooth_inverse
    (contDiff_localized_form ρ ω (some i) (fun x hx => hω.contDiffAt
      (hU.mem_nhds (hρU (some i) hx))))
    (hasCompactSupport_localized_form (fun i x => ρ i x) ω (some i) (hρc (some i)))
    (hsi.trans (a.patch i).domain_source)
    (fun x hx => (a.patch i).sublevel_iff (hsi hx))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LevelFace
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

lemma contDiff_coordinateFace {n : ℕ} (k : Fin (n+1)) (R : ℝ) :
    ContDiff ℝ 2 (coordinateFace k R) := by
  apply contDiff_pi.mpr
  rw [k.forall_iff_succAbove]
  constructor
  · simpa [coordinateFace] using (contDiff_const (c := R) : ContDiff ℝ 2 (fun _ : Fin n → ℝ => R))
  · intro j
    simpa [coordinateFace] using (contDiff_apply ℝ ℝ j : ContDiff ℝ 2 (fun y : Fin n → ℝ => y j))

lemma hasFDerivAt_coordinateFace {n : ℕ} (k : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (coordinateFace k R) (faceLinear k) y := by
  apply hasFDerivAt_pi.mpr
  rw [k.forall_iff_succAbove]
  constructor
  · simpa [coordinateFace, faceLinear] using (hasFDerivAt_const R y)
  · intro j
    simpa [coordinateFace, faceLinear] using (hasFDerivAt_apply j y)

lemma faceLinear_basis {n : ℕ} (k : Fin (n+1)) (j : Fin n) :
    faceLinear k (coordinateBasis n j) = k.removeNth (coordinateBasis (n+1)) j := by
  ext i
  revert i
  rw [k.forall_iff_succAbove]
  constructor
  · simp [faceLinear, coordinateBasis, Fin.removeNth]
  · intro i
    simp [faceLinear, coordinateBasis, Fin.removeNth, Pi.single_apply]

/-- The coefficient on a coordinate boundary face equals the actual
pullback coefficient of its lower-dimensional parametrization. -/
theorem pullback_coordinateFace_coefficient {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Fin (n+1)) (R : ℝ) (ψ : (Fin (n+1) → ℝ) → E)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) (y : Fin n → ℝ)
    (hψ : DifferentiableAt ℝ ψ (coordinateFace k R y)) :
    pullbackForm (fun z => ψ (coordinateFace k R z)) ω y (coordinateBasis n) =
      pullbackForm ψ ω (coordinateFace k R y) (k.removeNth (coordinateBasis (n+1))) := by
  have hd := hψ.hasFDerivAt.comp y (hasFDerivAt_coordinateFace k R y)
  change HasFDerivAt (fun z => ψ (coordinateFace k R z)) _ y at hd
  unfold pullbackForm
  rw [hd.fderiv]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply, faceLinear_basis]

namespace RegularBoundaryPatch
variable {n : ℕ} {U : Set (Fin (n+1) → ℝ)} {g : (Fin (n+1) → ℝ) → ℝ}

 theorem isOpen_faceDomain (p : RegularBoundaryPatch (n+1) U g) (R : ℝ) : IsOpen (p.faceDomain R) :=
  ((p.chart.symm.continuousOn.isOpen_inter_preimage p.chart.open_target p.open_domain).preimage
    (contDiff_coordinateFace p.coordinate R).continuous)

 theorem faceParam_mem (p : RegularBoundaryPatch (n+1) U g) (R : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R) : p.faceParam R y ∈ p.domain := hy.2

 theorem contDiffAt_faceParam (p : RegularBoundaryPatch (n+1) U g) (R : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R) : ContDiffAt ℝ 2 (p.faceParam R) y :=
  (p.smooth_inverse.contDiffAt (p.chart.open_target.mem_nhds hy.1)).comp y
    (contDiff_coordinateFace p.coordinate R).contDiffAt

/-- This parametrizes the actual regular level; the level equation is
proved from the inverse chart identity. -/
theorem level_faceParam (p : RegularBoundaryPatch (n+1) U g) (R : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R) : g (p.faceParam R y) = R := by
  have h := congrFun (p.chart.right_inv hy.1) p.coordinate
  rw [p.chart_eq] at h
  simpa [faceParam, levelCoordinates, coordinateFace] using h
end RegularBoundaryPatch

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LevelForms
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

lemma contDiffAt_energy_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    ContDiffAt ℝ 2 (energy f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  apply ContDiffAt.sum
  intro j hj
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)

omit [FiniteDimensional ℂ E] in
lemma dc_logTau_eq_div [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    dc (logTau f) x v = dc (energy f) x v / energy f x := by
  have hp : energy f x ∈ slitPlane := by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht
  have hh := ((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x
    (differentiable_energy hf).hasFDerivAt
  change HasFDerivAt (fun y => Complex.log (energy f y)) _ x at hh
  rw [logTau_eq, dc, hh.fderiv]
  simp [dc]
  ring

/-- On tangent vectors to an energy level, the actual exterior log form is
energy^{-1} times the energy form. This is local calculus, not Stokes. -/
theorem extDeriv_logTau_on_level {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (v w : E)
    (hv : fderiv ℝ (energy f) x v = 0) (hw : fderiv ℝ (energy f) x w = 0) :
    extDeriv (oneForm (dcLinear (logTau f))) x ![v, w] =
      (energy f x)⁻¹ * extDeriv (oneForm (dcLinear (energy f))) x ![v, w] := by
  have he := contDiffAt_energy_of_open hU hx hf
  have hde := differentiableAt_dcLinear he
  have hdl := differentiableAt_dcLinear (contDiffAt_logTau_of_open hU hx hf ht)
  have hfe := differentiable_energy (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx))
  have hn : energy f x ≠ 0 := by rw [energy_eq_tau]; exact_mod_cast ne_of_gt ht
  have hc : ContinuousAt (tau f) x := tau_continuousAt
    (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx))
  have hval (a b : E) (hb : fderiv ℝ (energy f) x b = 0) :
      fderiv ℝ (fun y => dcLinear (logTau f) y a) x b =
        (energy f x)⁻¹ * fderiv ℝ (fun y => dcLinear (energy f) y a) x b := by
    have heq : (fun y => dcLinear (logTau f) y a) =ᶠ[𝓝 x]
        (fun y => (energy f y)⁻¹ * dcLinear (energy f) y a) := by
      filter_upwards [hU.mem_nhds hx, hc.eventually (lt_mem_nhds ht)] with y hy hty
      simp only [dcLinear_apply, dc_logTau_eq_div
        (fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)) hty, div_eq_mul_inv]
      ring
    rw [heq.fderiv_eq]
    have hi := ((hasDerivAt_inv hn).hasFDerivAt.restrictScalars ℝ).comp x hfe.hasFDerivAt
    have ha := hde.hasFDerivAt.clm_apply (hasFDerivAt_const a x)
    have hh := hi.mul ha
    change HasFDerivAt (fun y => (energy f y)⁻¹ * dcLinear (energy f) y a) _ x at hh
    rw [hh.fderiv]
    have hae := congrArg (fun L : E →L[ℝ] ℂ => L b) ha.fderiv
    simp at hae
    simp [hb, hae]
  rw [extDeriv_oneForm hdl, extDeriv_oneForm hde, hval w v hv, hval v w hw]
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PuncturedBallStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_PunctureCutoff
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem continuousOn_extDeriv_coefficient {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) :
    ContinuousOn (fun x => extDeriv ω x (coordinateBasis (n+1))) U := by
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin (n+1) → ℝ) ℝ (n := n)
  let V := ContinuousAlternatingMap.apply ℝ (Fin (n+1) → ℝ) ℝ (coordinateBasis (n+1))
  intro x hx
  exact (V.continuous.continuousAt.comp (A.continuous.continuousAt.comp
    ((hω.contDiffAt (hU.mem_nhds hx)).continuousAt_fderiv one_ne_zero))).continuousWithinAt

 theorem integrableOn_extDeriv_compact_closure {n : ℕ} {U D : Set (Fin (n+1) → ℝ)}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (hc : IsCompact (closure D))
    (hDU : closure D ⊆ U) :
    IntegrableOn (fun x => extDeriv ω x (coordinateBasis (n+1))) D :=
  (((continuousOn_extDeriv_coefficient hU hω).mono hDU).integrableOn_compact hc).mono_set subset_closure

/-- An actual smooth cutoff removes the singularity at zero and is exactly
one on a neighborhood of every point outside the chosen open ball. -/
theorem exists_puncture_regularization {d n : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω (U \ {0})) :
    ∃ η : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ,
      ContDiffOn ℝ 1 η U ∧
      (∀ x ∉ coordBall d r, η =ᶠ[𝓝 x] ω) := by
  have hBo : IsOpen (coordBall d r) := isOpen_lt (continuous_radiusSq d) continuous_const
  have h0 : (0 : Fin d → ℝ) ∈ coordBall d r := by
    simpa [coordBall, radiusSq] using sq_pos_of_pos hr
  have hdis : Disjoint ({0} : Set (Fin d → ℝ)) (coordBall d r)ᶜ := by
    simp [h0]
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin d → ℝ) isClosed_singleton hBo.isClosed_compl hdis (n := 1)
  have hχ : ContDiff ℝ 1 χ := χ.contMDiff.contDiff
  have hχzero : (fun x => χ x) =ᶠ[𝓝 (0 : Fin d → ℝ)] (fun _ => 0) := by
    rw [nhdsSet_singleton] at hχ0
    filter_upwards [hχ0] with x hx
    exact hx
  refine ⟨fun x => χ x • ω x, ?_, ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    by_cases hx0 : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ))).congr_of_eventuallyEq
      filter_upwards [hχzero] with z hz
      simp [hz]
    · exact hχ.contDiffAt.smul (hω.contDiffAt
        ((hU.sdiff isClosed_singleton).mem_nhds ⟨hx, by simpa using hx0⟩))
  · intro x hx
    have hone : ∀ᶠ y in 𝓝 x, χ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hone] with y hy
    simp [hy]

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

 theorem integral_closedBall_eq_ball {n : ℕ} (r : ℝ) (f : (Fin (n+1) → ℝ) → ℝ) :
    (∫ x in coordClosedBall (n+1) r, f x) = ∫ x in coordBall (n+1) r, f x := by
  apply setIntegral_congr_set
  have hae : ∀ᵐ x : Fin (n+1) → ℝ, x ∉ {x | radiusSq x = r^2} :=
    ae_iff.mpr (by simpa using volume_coordSphere (n := n) r)
  filter_upwards [hae] with x hx
  apply propext
  change radiusSq x ≤ r^2 ↔ radiusSq x < r^2
  exact (lt_iff_le_and_ne.trans (and_iff_left hx)).symm

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

 theorem chartBoundaryFlux_congr {n : ℕ}
    (e : OpenPartialHomeomorph (Fin (n+1) → ℝ) (Fin (n+1) → ℝ))
    (k : Fin (n+1)) (R : ℝ)
    (ω η : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (he : ∀ x ∈ e.source, e x k = R → ω x = η x) :
    chartBoundaryFlux e k R ω = chartBoundaryFlux e k R η := by
  unfold chartBoundaryFlux
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : k.insertNth R y ∈ e.target
  · have hlevel : e (e.symm (k.insertNth R y)) k = R := by rw [e.right_inv hy]; simp
    simp [extendedChartForm, hy, pullbackForm, he _ (e.map_target hy) hlevel]
  · simp [extendedChartForm, hy]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PuncturedSublevelStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- Punctured Stokes for a fixed atlas and partition, allowing comparison
with another form on the very same oriented boundary representation. -/
theorem punctured_sublevel_stokes_of_partition {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R r : ℝ}
    (hU : IsOpen U) (hg : ContinuousOn g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hr : 0 < r) (hB : coordClosedBall (n+1) r ⊆ regularSublevel U g R)
    (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
    {W : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
      (Fin (n+1) → ℝ) (closure W))
    (hWo : IsOpen W) (hCW : closure (regularSublevel U g R) ⊆ W)
    (hρc : ∀ i, HasCompactSupport (ρ i)) (hρsub : ρ.IsSubordinate (sublevelPatchDomain a))
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω (U \ {0})) :
    (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
      (fun z => ρ (some i) z • ω z)) - sphereFlux r ω =
      ∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
        extDeriv ω x (coordinateBasis (n+1)) := by
  obtain ⟨η, hη, hηeq⟩ := exists_puncture_regularization hU hr ω hω
  have hstokes := integral_extDeriv_regular_partition hU hg a ρ hWo hCW hρc hρsub hsum η hη
  have hD : MeasurableSet (regularSublevel U g R) :=
    (isOpen_regularSublevel hU hg).measurableSet
  have hCB : MeasurableSet (coordClosedBall (n+1) r) :=
    (isCompact_coordClosedBall (n+1) r).measurableSet
  have htrace (i : a.Index) :
      chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R (fun z => ρ (some i) z • η z) =
      chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R (fun z => ρ (some i) z • ω z) := by
    apply chartBoundaryFlux_congr
    intro x _ hxlevel
    by_cases hz : ρ (some i) x = 0
    · simp [hz]
    · have hxU : x ∈ U := (a.patch i).domain_U (hρsub (some i) (subset_tsupport (ρ (some i)) hz))
      have hxg : g x = R := by
        simpa [RegularBoundaryPatch.chart_eq, levelCoordinates] using hxlevel
      have hxB : x ∉ coordBall (n+1) r := by
        intro h
        have hlt := (hB (show x ∈ coordClosedBall (n+1) r from (show radiusSq x < r^2 from h).le)).2
        exact (ne_of_lt hlt) hxg
      rw [(hηeq x hxB).self_of_nhds]
  have hsphere : sphereFlux r η = sphereFlux r ω := by
    apply sphereFlux_congr
    intro x hx
    exact (hηeq x (by change ¬radiusSq x < r^2; rw [hx]; exact lt_irrefl _)).self_of_nhds
  have hball : (∫ x in coordClosedBall (n+1) r, extDeriv η x (coordinateBasis (n+1))) =
      sphereFlux r η := by
    rw [integral_closedBall_eq_ball]
    exact integral_extDeriv_ball_local r η hU hη (hB.trans inter_subset_left)
  have hvolume :
      (∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
        extDeriv ω x (coordinateBasis (n+1))) =
      (∫ x in regularSublevel U g R, extDeriv η x (coordinateBasis (n+1))) - sphereFlux r η := by
    calc
      _ = ∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
          extDeriv η x (coordinateBasis (n+1)) := by
        apply setIntegral_congr_fun (hD.diff hCB)
        intro x hx
        have hxB : x ∉ coordBall (n+1) r := fun h => hx.2 (show x ∈ coordClosedBall (n+1) r from (show radiusSq x < r^2 from h).le)
        dsimp only
        rw [(hηeq x hxB).extDeriv_eq]
      _ = _ := (setIntegral_sdiff hCB
        (integrableOn_extDeriv_compact_closure hU hη hc hcl) hB).trans (by rw [hball])
  rw [hstokes, hsphere] at hvolume
  simp_rw [htrace] at hvolume
  exact hvolume.symm

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ReferenceSphere
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

/-- Restriction to any linear space of vectors tangent to an energy level. -/
theorem level_oneForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E) :
    (oneForm (dcLinear (logTau f)) x).toAlternatingMap.compLinearMap S.subtype =
      (energy f x)⁻¹ •
        (oneForm (dcLinear (energy f)) x).toAlternatingMap.compLinearMap S.subtype := by
  ext v
  change dcLinear (logTau f) x (v 0) = (energy f x)⁻¹ * dcLinear (energy f) x (v 0)
  rw [dcLinear_apply, dcLinear_apply,
    dc_logTau_eq_div (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx)) ht]
  ring

theorem level_twoForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E)
    (hS : ∀ v : S, fderiv ℝ (energy f) x v = 0) :
    (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap.compLinearMap S.subtype =
      (energy f x)⁻¹ •
        (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap.compLinearMap S.subtype := by
  ext v
  change extDeriv (oneForm (dcLinear (logTau f))) x (fun i => (v i : E)) =
    (energy f x)⁻¹ * extDeriv (oneForm (dcLinear (energy f))) x (fun i => (v i : E))
  have hv : (fun i => (v i : E)) = ![(v 0 : E), (v 1 : E)] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact extDeriv_logTau_on_level hU hx hf ht (v 0) (v 1) (hS (v 0)) (hS (v 1))

/-- The complete boundary form scales by tau^(-(k+1)), with the actual
shuffle exterior power. No integration identity is assumed. -/
theorem level_boundaryForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E)
    (hS : ∀ v : S, fderiv ℝ (energy f) x v = 0) (k : ℕ) :
    wedge ((oneForm (dcLinear (logTau f)) x).toAlternatingMap.compLinearMap S.subtype)
      (wedgePower ((extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap.compLinearMap S.subtype) k) =
    ((energy f x)⁻¹) ^ (k+1) •
      wedge ((oneForm (dcLinear (energy f)) x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap.compLinearMap S.subtype) k) := by
  rw [level_oneForm_scaling hU hx hf ht S, level_twoForm_scaling hU hx hf ht S hS,
    wedgePower_smul, wedge_smul_left, wedge_smul_right, smul_smul, pow_succ']

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceLevelFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- Smoothness of the literal energy, at any finite order, is derived from
first-order holomorphicity on the open source domain. -/
theorem MassHypotheses.contDiffAt_energy (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) :
    ContDiffAt ℝ r (energy f) x := by
  apply ContDiffAt.sum
  intro j _
  have hj : ContDiffAt ℝ r (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open h.open_domain r (h.holomorphic j)).contDiffAt
      (h.open_domain.mem_nhds hx)).restrict_scalars ℝ
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x hj).mul hj

theorem MassHypotheses.tau_pos (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) : 0 < tau f x := by
  have hnot : ¬∀ j, f j x = 0 := fun hz => hne ((h.isolated_zero x hx).mp hz)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

theorem MassHypotheses.contDiffAt_logTau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) (r : ℕ) :
    ContDiffAt ℝ r (logTau f) x := by
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := r) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr (h.tau_pos hx hne))).restrict_scalars ℝ).comp x
    (h.contDiffAt_energy hx r)

/-- Full scaling on any parametrization of a positive level.
The tangent condition follows by differentiating its level equation. -/
theorem sourceBoundaryForm_level_pullback {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ : V → ComplexEuclidean n} {y : V} {R : ℝ}
    (h : MassHypotheses n N m U f G) (hR : 0 < R) (hx : φ y ∈ U)
    (hφ : DifferentiableAt ℝ φ y)
    (hlevel : (fun z => tau f (φ z)) =ᶠ[𝓝 y] (fun _ => R)) (k : ℕ) :
    (sourceBoundaryForm (logTau f) k (φ y)).compLinearMap (fderiv ℝ φ y).toLinearMap =
      ((R : ℂ)⁻¹)^(k+1) •
        (sourceBoundaryForm (energy f) k (φ y)).compLinearMap (fderiv ℝ φ y).toLinearMap := by
  have hval : tau f (φ y) = R := hlevel.self_of_nhds
  have he : (energy f ∘ φ) =ᶠ[𝓝 y] (fun _ => (R : ℂ)) := by
    filter_upwards [hlevel] with z hz
    simp [energy_eq_tau, hz]
  have hd := (h.contDiffAt_energy hx 1).differentiableAt (by simp)
  have hz := congrArg (fun L : V →L[ℝ] ℂ => L)
    ((hd.hasFDerivAt.comp y hφ.hasFDerivAt).fderiv.symm.trans he.fderiv_eq)
  rw [(hasFDerivAt_const (R : ℂ) y).fderiv] at hz
  let S := LinearMap.range (fderiv ℝ φ y).toLinearMap
  have ht (v : S) : fderiv ℝ (energy f) (φ y) v = 0 := by
    obtain ⟨w, hw⟩ := v.property
    change (fderiv ℝ φ y) w = (v : ComplexEuclidean n) at hw
    have hv := congrArg (fun L : V →L[ℝ] ℂ => L w) hz
    change fderiv ℝ (energy f) (φ y) ((fderiv ℝ φ y) w) = 0 at hv
    rw [hw] at hv
    exact hv
  have hs := level_boundaryForm_scaling h.open_domain hx h.holomorphic
    (hval.symm ▸ hR) S ht k
  have hs' : (sourceBoundaryForm (logTau f) k (φ y)).compLinearMap S.subtype =
      ((R : ℂ)⁻¹)^(k+1) •
        (sourceBoundaryForm (energy f) k (φ y)).compLinearMap S.subtype := by
    unfold sourceBoundaryForm
    simp only [wedge_compLinearMap, wedgePower_compLinearMap]
    simpa only [energy_eq_tau, hval] using hs
  have htup (v : Fin 1 ⊕ WedgePowerSlots k → V) :
      ∀ i, (fderiv ℝ φ y) (v i) ∈ S := fun i => ⟨v i, rfl⟩
  ext v
  have hv := congrArg (fun a => a (fun i => (⟨(fderiv ℝ φ y) (v i), htup v i⟩ : S))) hs'
  exact hv

/-- Instantiation on the actual regular boundary charts constructed by Stokes. -/
theorem sourceBoundaryForm_regular_face {d : ℕ}
    (h : MassHypotheses n N m U f G)
    (Ψ : (Fin (d+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    (p : MahlerStokes.RegularBoundaryPatch (d+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x)))
    {R : ℝ} (hR : 0 < R) {y : Fin d → ℝ} (hy : y ∈ p.faceDomain R) (k : ℕ) :
    (sourceBoundaryForm (logTau f) k (Ψ (p.faceParam R y))).compLinearMap
      (fderiv ℝ (fun z => Ψ (p.faceParam R z)) y).toLinearMap =
      ((R : ℂ)⁻¹)^(k+1) •
        (sourceBoundaryForm (energy f) k (Ψ (p.faceParam R y))).compLinearMap
          (fderiv ℝ (fun z => Ψ (p.faceParam R z)) y).toLinearMap := by
  have hφ : DifferentiableAt ℝ (fun z => Ψ (p.faceParam R z)) y :=
    Ψ.differentiableAt.comp y
      ((p.contDiffAt_faceParam R hy).differentiableAt (by norm_num))
  have he : (fun z => tau f (Ψ (p.faceParam R z))) =ᶠ[𝓝 y] (fun _ => R) := by
    filter_upwards [(p.isOpen_faceDomain R).mem_nhds hy] with z hz
    exact p.level_faceParam R hz
  exact sourceBoundaryForm_level_pullback (φ := fun z => Ψ (p.faceParam R z))
    (y := y) h hR (p.domain_U (p.faceParam_mem R hy)) hφ he k

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceFluxRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_sourceDC [FiniteDimensional ℝ E] {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+1) u x) : ContDiffAt ℝ r (oneForm (dcLinear u)) x := by
  have hd : ContDiffAt ℝ r (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact sourceDCOperator.contDiff.contDiffAt.comp x hd

lemma contDiffAt_sourceDDC {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+2) u x) :
    ContDiffAt ℝ r (extDeriv (oneForm (dcLinear u))) x := by
  have hd : ContDiffAt ℝ (r+1) (oneForm (dcLinear u)) x :=
    contDiffAt_sourceDC (by convert hu using 1 ; norm_num [add_assoc])
  have hdd : ContDiffAt ℝ r (fderiv ℝ (oneForm (dcLinear u))) x :=
    hd.fderiv_right (by norm_num)
  exact (alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x hdd

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma continuousWedgePower_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] (a : E [⋀^Fin 2]→L[ℝ] ℂ) (k : ℕ) :
    (continuousWedgePower a k).toAlternatingMap = wedgePower a.toAlternatingMap k := by
  induction k with
  | zero => rfl
  | succ k ih => change wedge _ _ = _; rw [ih]; rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_continuousWedgePower [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → E [⋀^Fin 2]→L[ℝ] ℂ} {x : X} {r : WithTop ℕ∞}
    (ha : ContDiffAt ℝ r a x) (k : ℕ) :
    ContDiffAt ℝ r (fun y => continuousWedgePower (a y) k) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih => exact contDiffAt_continuousWedge ha ih

lemma continuousSourceBoundaryForm_eq {n : ℕ} (u : ComplexEuclidean n → ℂ)
    (k : ℕ) (x : ComplexEuclidean n) :
    (continuousSourceBoundaryForm u k x).toAlternatingMap = sourceBoundaryForm u k x := by
  unfold continuousSourceBoundaryForm sourceBoundaryForm
  change wedge _ _ = _
  rw [continuousWedgePower_toAlternatingMap]

lemma continuousSourceBoundaryForm_apply {n : ℕ} (u : ComplexEuclidean n → ℂ)
    (k : ℕ) (x : ComplexEuclidean n) (v : Fin 1 ⊕ WedgePowerSlots k → ComplexEuclidean n) :
    continuousSourceBoundaryForm u k x v = sourceBoundaryForm u k x v :=
  congrArg (fun a => a v) (continuousSourceBoundaryForm_eq u k x)

/-- C1 regularity of the whole actual flux form uses C3 of its potential. -/
theorem contDiffAt_sourceBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (continuousSourceBoundaryForm u k) x := by
  exact contDiffAt_continuousWedge
    (contDiffAt_sourceDC (hu.of_le (by norm_num) : ContDiffAt ℝ (1+1) u x))
    (contDiffAt_continuousWedgePower
      (contDiffAt_sourceDDC (hu : ContDiffAt ℝ (1+2) u x)) k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceCoordinateForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Set Filter MeasureTheory
open scoped Topology Manifold

namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [FiniteDimensional ℝ E] in
lemma sourceRealBoundaryForm_apply [FiniteDimensional ℝ E] (u : E → ℂ) (k : ℕ) (x : E)
    (v : Fin (2*k+1) → E) :
    sourceRealBoundaryForm u k x v =
      (continuousSourceBoundaryForm u k x (fun s => v (sourceBoundarySlots k s))).re := rfl

lemma contDiffAt_sourceRealBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (sourceRealBoundaryForm u k) x := by
  exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin (2*k+1))
      Complex.reCLM).contDiff.contDiffAt.comp x
    ((sourceReindexCLM (E := E) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
      (contDiffAt_sourceBoundaryForm hu k)))

lemma contDiffAt_sourceCoordinateForm {d : ℕ}
    (Ψ : (Fin d → ℝ) ≃L[ℝ] E) {u : E → ℂ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ 3 u (Ψ x)) (k : ℕ) :
    ContDiffAt ℝ 1 (sourceCoordinateForm Ψ u k) x := by
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM Ψ.toContinuousLinearMap).contDiff.contDiffAt.comp x
    ((contDiffAt_sourceRealBoundaryForm hu k).comp x Ψ.contDiff.contDiffAt)

variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.contDiffOn_coordinateEnergy (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (k : ℕ) :
    ContDiffOn ℝ 1 (sourceCoordinateForm Ψ (energy f) k) (Ψ ⁻¹' U) := by
  intro x hx
  exact (contDiffAt_sourceCoordinateForm Ψ (h.contDiffAt_energy hx 3) k).contDiffWithinAt

theorem MassHypotheses.contDiffOn_coordinateLog (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (k : ℕ) :
    ContDiffOn ℝ 1 (sourceCoordinateForm Ψ (logTau f) k) ((Ψ ⁻¹' U) \ {0}) := by
  intro x hx
  have hn : Ψ x ≠ 0 := by
    intro hz
    have : x = 0 := Ψ.injective (by simpa using hz)
    exact hx.2 (by simpa using this)
  exact (contDiffAt_sourceCoordinateForm Ψ (h.contDiffAt_logTau hx.1 hn 3) k).contDiffWithinAt

/-- The level equation holds on the open chart-face domain;
this theorem applies the full R^(-(k+1)) law to the real Stokes form. -/
theorem sourceCoordinateForm_regular_face {d : ℕ}
    (h : MassHypotheses n N m U f G)
    (Ψ : (Fin (d+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    (p : MahlerStokes.RegularBoundaryPatch (d+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x)))
    {R : ℝ} (hR : 0 < R) {y : Fin d → ℝ} (hy : y ∈ p.faceDomain R) (k : ℕ) :
    MahlerStokes.pullbackForm (p.faceParam R) (sourceCoordinateForm Ψ (logTau f) k) y =
      (R⁻¹)^(k+1) •
        MahlerStokes.pullbackForm (p.faceParam R) (sourceCoordinateForm Ψ (energy f) k) y := by
  have hd := Ψ.hasFDerivAt.comp y
    ((p.contDiffAt_faceParam R hy).differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun z => Ψ (p.faceParam R z)) _ y at hd
  have hs := sourceBoundaryForm_regular_face h Ψ p hR hy k
  rw [hd.fderiv] at hs
  ext v
  have he := congrArg (fun a => (a (fun s => v (sourceBoundarySlots k s))).re) hs
  simpa only [MahlerStokes.pullbackForm, sourceCoordinateForm, sourceRealBoundaryForm_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_def, continuousSourceBoundaryForm_apply, ContinuousLinearMap.coe_coe,
    AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, ← Complex.ofReal_inv,
    ← Complex.ofReal_pow, Complex.real_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using he

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes
open scoped Topology Manifold

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.contDiffAt_tau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) : ContDiffAt ℝ r (tau f) x := by
  have he : (fun z => (energy f z).re) = tau f := by
    funext z; simp only [energy_eq_tau, Complex.ofReal_re]
  rw [← he]
  exact Complex.reCLM.contDiff.contDiffAt.comp x (h.contDiffAt_energy hx r)

theorem MassHypotheses.contDiffOn_coordinateTau (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (r : ℕ) :
    ContDiffOn ℝ r (fun x => tau f (Ψ x)) (Ψ ⁻¹' U) := by
  intro x hx
  exact ((h.contDiffAt_tau hx r).comp x Ψ.contDiff.contDiffAt).contDiffWithinAt

lemma source_sublevel_preimage {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (R : ℝ) :
    regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R =
      Ψ ⁻¹' (U ∩ {x | tau f x < R}) := rfl

theorem MassHypotheses.coordinate_compact_sublevels (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R)) ∧
      closure (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) ⊆ Ψ ⁻¹' U := by
  have he : closure (Ψ ⁻¹' (U ∩ {x | tau f x < R})) =
      Ψ ⁻¹' closure (U ∩ {x | tau f x < R}) :=
    (Ψ.toHomeomorph.preimage_closure (U ∩ {x | tau f x < R})).symm
  rw [source_sublevel_preimage, he]
  obtain ⟨hc, hs⟩ := h.compact_sublevels R hR hR1
  exact ⟨Ψ.toHomeomorph.isCompact_preimage.mpr hc, preimage_mono hs⟩

theorem MassHypotheses.coordinate_regular (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) {R : ℝ}
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0) :
    ∀ x ∈ Ψ ⁻¹' U, tau f (Ψ x) = R → fderiv ℝ (fun y => tau f (Ψ y)) x ≠ 0 := by
  intro x hx he hz
  have hd := ((h.contDiffAt_tau hx 1).differentiableAt (by norm_num)).hasFDerivAt.comp x Ψ.hasFDerivAt
  change HasFDerivAt (fun y => tau f (Ψ y)) _ x at hd
  rw [hd.fderiv] at hz
  apply hreg (Ψ x) hx he
  ext v
  have hv := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Ψ.symm v)) hz
  simpa using hv

/-- A single regular-level atlas and partition yield
Stokes identities for both coordinate forms. The punctured identity holds for every
admissible inner radius with that same outer representation. No differential
identity or positivity is a premise. Identification of the
integrands with top wedge powers is not asserted here. -/
theorem exists_source_stokes_partition (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0) :
    ∃ (a : RegularBoundaryAtlas ((2*k+1)+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x))
        (frontier (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R)))
      (W : Set (Fin ((2*k+1)+1) → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin ((2*k+1)+1) → ℝ)
        (Fin ((2*k+1)+1) → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) ⊆ W ∧
      (∀ i, HasCompactSupport (ρ i)) ∧ ρ.IsSubordinate (sublevelPatchDomain a) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) ∧
      (∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R,
        extDeriv (sourceCoordinateForm Ψ (energy f) k) x (coordinateBasis ((2*k+1)+1))) =
        (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • sourceCoordinateForm Ψ (energy f) k z)) ∧
      (∀ r : ℝ, 0 < r →
        coordClosedBall ((2*k+1)+1) r ⊆ regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R →
        (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • sourceCoordinateForm Ψ (logTau f) k z)) -
            _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm Ψ (logTau f) k) =
          ∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R \ coordClosedBall ((2*k+1)+1) r,
            extDeriv (sourceCoordinateForm Ψ (logTau f) k) x (coordinateBasis ((2*k+1)+1))) := by
  have ho : IsOpen (Ψ ⁻¹' U) := h.open_domain.preimage Ψ.continuous
  have hg := h.contDiffOn_coordinateTau Ψ 2
  obtain ⟨hc, hcl⟩ := h.coordinate_compact_sublevels Ψ hR hR1
  obtain ⟨a⟩ := exists_sublevelBoundaryAtlas ho hg hc hcl (h.coordinate_regular Ψ hreg)
  obtain ⟨W, ρ, hWo, hCW, _, hρsub, hρc, hsum⟩ :=
    exists_sublevel_partition ho hg.continuousOn hc a
  refine ⟨a, W, ρ, hWo, hCW, hρc, hρsub, hsum, ?_, ?_⟩
  · exact integral_extDeriv_regular_partition ho hg.continuousOn a ρ hWo hCW hρc hρsub hsum
      (sourceCoordinateForm Ψ (energy f) k) (h.contDiffOn_coordinateEnergy Ψ k)
  · intro r hr hB
    exact punctured_sublevel_stokes_of_partition ho hg.continuousOn hc hcl hr hB
      a ρ hWo hCW hρc hρsub hsum (sourceCoordinateForm Ψ (logTau f) k)
      (h.contDiffOn_coordinateLog Ψ k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceBoundaryIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes
open scoped Topology Manifold

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The R^(-(k+1)) boundary restriction survives the actual oriented chart
integral, including its compact cutoff and its zero extension. -/
theorem chartBoundaryFlux_source_scaling (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    (p : RegularBoundaryPatch ((2*k+1)+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x)))
    {R : ℝ} (hR : 0 < R) (ρ : (Fin ((2*k+1)+1) → ℝ) → ℝ)
    (hρ : tsupport ρ ⊆ p.domain) :
    chartBoundaryFlux p.chart p.coordinate R (fun z => ρ z • sourceCoordinateForm Ψ (logTau f) k z) =
      (R⁻¹)^(k+1) * chartBoundaryFlux p.chart p.coordinate R
        (fun z => ρ z • sourceCoordinateForm Ψ (energy f) k z) := by
  have he (y : Fin (2*k+1) → ℝ) :
      extendedChartForm p.chart (fun z => ρ z • sourceCoordinateForm Ψ (logTau f) k z)
        (p.coordinate.insertNth R y) (p.coordinate.removeNth (coordinateBasis ((2*k+1)+1))) =
      (R⁻¹)^(k+1) * extendedChartForm p.chart
        (fun z => ρ z • sourceCoordinateForm Ψ (energy f) k z)
          (p.coordinate.insertNth R y) (p.coordinate.removeNth (coordinateBasis ((2*k+1)+1))) := by
    by_cases hy : p.coordinate.insertNth R y ∈ p.chart.target
    · by_cases hz : ρ (p.chart.symm (p.coordinate.insertNth R y)) = 0
      · simp [extendedChartForm, hy, pullbackForm, hz]
      · have hdom : p.chart.symm (p.coordinate.insertNth R y) ∈ p.domain :=
          hρ (subset_tsupport ρ hz)
        have hface : y ∈ p.faceDomain R := ⟨hy, hdom⟩
        have hψ : DifferentiableAt ℝ p.chart.symm (coordinateFace p.coordinate R y) :=
          (p.smooth_inverse.contDiffAt (p.chart.open_target.mem_nhds hy)).differentiableAt (by norm_num)
        have hf := congrArg (fun a => a (coordinateBasis (2*k+1)))
          (sourceCoordinateForm_regular_face h Ψ p hR hface k)
        simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hf
        unfold RegularBoundaryPatch.faceParam at hf
        rw [pullback_coordinateFace_coefficient p.coordinate R p.chart.symm _ y hψ,
          pullback_coordinateFace_coefficient p.coordinate R p.chart.symm _ y hψ] at hf
        simp only [pullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply] at hf
        simp only [extendedChartForm, indicator_of_mem hy, pullbackForm,
          ContinuousAlternatingMap.compContinuousLinearMap_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        unfold coordinateFace at hf
        rw [hf]
        ring
    · simp [extendedChartForm, hy]
  unfold chartBoundaryFlux
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- The Stokes identity for coordinate flux forms, with all charts
eliminated from the conclusion. The volume integrands are
exterior derivatives of those forms; equality to Hessian top
powers is not asserted by this theorem. -/
theorem source_punctured_scaled_extDeriv_oai (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R r : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0)
    (hr : 0 < r)
    (hB : coordClosedBall ((2*k+1)+1) r ⊆ regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) :
    (R⁻¹)^(k+1) *
      (∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R,
        extDeriv (sourceCoordinateForm Ψ (energy f) k) x (coordinateBasis ((2*k+1)+1))) -
      _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm Ψ (logTau f) k) =
      ∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R \ coordClosedBall ((2*k+1)+1) r,
        extDeriv (sourceCoordinateForm Ψ (logTau f) k) x (coordinateBasis ((2*k+1)+1)) := by
  obtain ⟨a, W, ρ, _, _, _, hρsub, _, hE, hL⟩ :=
    exists_source_stokes_partition h k Ψ hR hR1 hreg
  have hs :
      (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
        (fun z => ρ (some i) z • sourceCoordinateForm Ψ (logTau f) k z)) =
      (R⁻¹)^(k+1) *
        (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • sourceCoordinateForm Ψ (energy f) k z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact chartBoundaryFlux_source_scaling h k Ψ (a.patch i) hR (ρ (some i)) (hρsub (some i))
  have hl := hL r hr hB
  rw [hs, ← hE] at hl
  exact hl

end
end Mahler

end OAI
end

theorem solution : type_of% @OAI.Mahler.source_punctured_scaled_extDeriv_oai := @OAI.Mahler.source_punctured_scaled_extDeriv_oai
