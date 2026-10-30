-- Prove2me | solution 1 for OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:06:02.034661+00:00
-- url     : https://prove2.me/submissions/9dce2025-f9f2-442b-b4a0-ca3270f540e6

import Mathlib
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WitnessTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving an actual popularity witness to a fixed reference line. -/

noncomputable section

open scoped NNReal

namespace LipschitzHilbert
namespace SlopeBox

theorem horizontal_sub_identity (T : SlopeBox) (z w : ℝ × ℝ) :
    w.1 - z.1 = T.length * (T.horizontal w - T.horizontal z) := by
  unfold horizontal
  field_simp [T.length_pos.ne']
  ring

theorem transverse_sub_identity (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ) :
    w.2 - (referencePoint s z w).2 =
      T.width * (T.transverse w - T.transverse z) +
        (T.slope - s) * (w.1 - z.1) := by
  unfold transverse referencePoint
  dsimp
  field_simp [T.width_pos.ne']
  ring

/-- Box coordinates give the vertical distance to the reference line using
only the two actual points, with no choice of a point in a projection fiber. -/
theorem referencePoint_vertical_distance (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ) :
    |w.2 - (referencePoint s z w).2| ≤
      (T.radius w + T.radius z) * (T.width + T.length * |T.slope - s|) := by
  have hzw : |w.1 - z.1| ≤ T.length * (T.radius w + T.radius z) := by
    rw [T.horizontal_sub_identity, abs_mul, abs_of_pos T.length_pos]
    have htri := abs_sub (T.horizontal w) (T.horizontal z)
    have hw : |T.horizontal w| ≤ T.radius w := by
      unfold radius
      linarith [abs_nonneg (T.transverse w)]
    have hz : |T.horizontal z| ≤ T.radius z := by
      unfold radius
      linarith [abs_nonneg (T.transverse z)]
    exact mul_le_mul_of_nonneg_left (htri.trans (add_le_add hw hz)) T.length_pos.le
  have htrans : |T.transverse w - T.transverse z| ≤ T.radius w + T.radius z := by
    have hw : |T.transverse w| ≤ T.radius w := by
      unfold radius
      linarith [abs_nonneg (T.horizontal w)]
    have hz : |T.transverse z| ≤ T.radius z := by
      unfold radius
      linarith [abs_nonneg (T.horizontal z)]
    exact (abs_sub _ _).trans (add_le_add hw hz)
  rw [T.transverse_sub_identity]
  calc
    _ ≤ |T.width * (T.transverse w - T.transverse z)| +
        |(T.slope - s) * (w.1 - z.1)| := abs_add_le _ _
    _ = T.width * |T.transverse w - T.transverse z| +
        |T.slope - s| * |w.1 - z.1| := by
      rw [abs_mul, abs_mul, abs_of_pos T.width_pos]
    _ ≤ T.width * (T.radius w + T.radius z) +
        |T.slope - s| * (T.length * (T.radius w + T.radius z)) :=
      add_le_add (mul_le_mul_of_nonneg_left htrans T.width_pos.le)
        (mul_le_mul_of_nonneg_left hzw (abs_nonneg _))
    _ = _ := by ring

theorem referencePoint_vertical_distance_le (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ)
    {A K : ℝ} (hw : T.radius w ≤ A) (hz : T.radius z ≤ K) :
    |w.2 - (referencePoint s z w).2| ≤
      (A + K) * (T.width + T.length * |T.slope - s|) := by
  exact (T.referencePoint_vertical_distance s z w).trans
    (mul_le_mul_of_nonneg_right (add_le_add hw hz) (by
      have hl := T.length_pos
      have hw := T.width_pos
      positivity))

/-- The two points have the same horizontal coordinate, so a Lipschitz slope
field loses precisely their vertical distance. -/
theorem referencePoint_slope_error (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ)
    (u : ℝ × ℝ → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) {δ A K : ℝ}
    (huw : |u w - T.slope| ≤ δ) (hw : T.radius w ≤ A) (hz : T.radius z ≤ K) :
    |u (referencePoint s z w) - T.slope| ≤
      δ + L * ((A + K) * (T.width + T.length * |T.slope - s|)) := by
  have hdist : dist (referencePoint s z w) w = |w.2 - (referencePoint s z w).2| := by
    simp [Prod.dist_eq, referencePoint, Real.dist_eq, abs_sub_comm]
  have hfield := hu.dist_le_mul (referencePoint s z w) w
  rw [Real.dist_eq, hdist] at hfield
  calc
    _ ≤ |u (referencePoint s z w) - u w| + |u w - T.slope| := abs_sub_le _ _ _
    _ ≤ L * |w.2 - (referencePoint s z w).2| + δ := add_le_add hfield huw
    _ ≤ L * ((A + K) * (T.width + T.length * |T.slope - s|)) + δ :=
      add_le_add (mul_le_mul_of_nonneg_left
        (T.referencePoint_vertical_distance_le s z w hw hz) L.coe_nonneg) le_rfl
    _ = _ := by ring

/-- The paper's small-time condition transfers a witness of precision `d`
to the reference line with angular error at most `(c+1)Δ/B²`. The width is
the actual enlarged width `m * length * d`, and `B² ≤ m`. -/
theorem transferred_slope_precision (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ)
    (u : ℝ × ℝ → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u)
    {d m B c A K P : ℝ} (hd : 0 ≤ d) (hB : 0 < B) (hc : 0 ≤ c)
    (hw : T.radius w ≤ A) (hz : T.radius z ≤ K) (hP : A + K ≤ P)
    (hwidth : T.width = m * T.length * d) (hm : B ^ 2 ≤ m)
    (hprecision : d ≤ |T.slope - s| / B ^ 2)
    (hsmall : L * P * m * T.length ≤ 1 / 2)
    (huw : |u w - T.slope| ≤ c * d) :
    |u (referencePoint s z w) - T.slope| ≤ (c + 1) * |T.slope - s| / B ^ 2 := by
  have hAK : 0 ≤ A + K := by
    linarith [T.radius_nonnegative w, T.radius_nonnegative z]
  have hP0 : 0 ≤ P := hAK.trans hP
  have hlength := T.length_pos
  have hwidth0 := T.width_pos
  let a : ℝ := L * P * T.length
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ham : a * m ≤ 1 / 2 := by dsimp [a]; nlinarith [hsmall]
  have haB : a * B ^ 2 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hm ha).trans ham
  have habound : a ≤ (1 / 2) / B ^ 2 := (le_div_iff₀ (sq_pos_of_pos hB)).2 haB
  have hwidthError : a * m * d ≤ (1 / 2) * (|T.slope - s| / B ^ 2) :=
    (mul_le_mul_of_nonneg_right ham hd).trans
      (mul_le_mul_of_nonneg_left hprecision (by norm_num))
  have hlengthError : a * |T.slope - s| ≤ (1 / 2) * (|T.slope - s| / B ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right habound (abs_nonneg (T.slope - s))
    calc
      _ ≤ (1 / 2) / B ^ 2 * |T.slope - s| := hh
      _ = _ := by ring
  have hmotion : L * ((A + K) * (T.width + T.length * |T.slope - s|)) ≤
      |T.slope - s| / B ^ 2 := by
    calc
      _ ≤ L * (P * (T.width + T.length * |T.slope - s|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hP (by positivity)) L.coe_nonneg
      _ = a * m * d + a * |T.slope - s| := by rw [hwidth]; dsimp [a]; ring
      _ ≤ _ := by linarith
  have hwitness := mul_le_mul_of_nonneg_left hprecision hc
  have herr := T.referencePoint_slope_error s z w u hu huw hw hz
  calc
    _ ≤ c * d + L * ((A + K) * (T.width + T.length * |T.slope - s|)) := herr
    _ ≤ c * (|T.slope - s| / B ^ 2) + |T.slope - s| / B ^ 2 :=
      add_le_add hwitness hmotion
    _ = _ := by ring

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_WitnessProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal projection size of actual compact popularity witnesses. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

/-- A compact set confined between two parallel lines has area at most its
horizontal projection length times its vertical thickness. -/
theorem projection_measure_bound (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {s c B : ℝ} (hB : 0 ≤ B)
    (hstrip : ∀ z ∈ E, |z.2 - s * z.1 - c| ≤ B) :
    (volume.prod volume).real E ≤ 2 * B * volume.real (Prod.fst '' E) := by
  let e := slopeShear (-s)
  have hecont : Continuous e := by
    change Continuous (fun z : ℝ × ℝ => (z.1, z.2 + -s * z.1))
    fun_prop
  have hproj : IsCompact (Prod.fst '' E) := hE.image continuous_fst
  have hsubset : e '' E ⊆ (Prod.fst '' E) ×ˢ Icc (c - B) (c + B) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    have hh := abs_le.mp (hstrip z hz)
    change c - B ≤ z.2 + -s * z.1 ∧ z.2 + -s * z.1 ≤ c + B
    constructor <;> linarith
  have hfinite : (volume.prod volume) ((Prod.fst '' E) ×ˢ Icc (c - B) (c + B)) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hproj.measure_lt_top.ne (by simp [Real.volume_Icc])
  have hbound := measureReal_mono hsubset hfinite
  rw [measureReal_prod_prod, Real.volume_real_Icc_of_le (by linarith)] at hbound
  have hpres := (slopeShear_measurePreserving (-s)).measure_preimage_equiv (e '' E)
  have hpreimage : e ⁻¹' (e '' E) = E := Set.preimage_image_eq E e.injective
  change (volume.prod volume) (e ⁻¹' (e '' E)) = (volume.prod volume) (e '' E) at hpres
  rw [hpreimage] at hpres
  have hreal : (volume.prod volume).real E = (volume.prod volume).real (e '' E) :=
    congrArg ENNReal.toReal hpres
  rw [hreal]
  calc
    _ ≤ volume.real (Prod.fst '' E) * (c + B - (c - B)) := hbound
    _ = _ := by ring

namespace SlopeBox

/-- The compact witness occupies a substantial horizontal set solely from
its area and the box-width bound. No measurable selection of fibers is used. -/
theorem witness_projection_lower (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q : ℝ} (hA : 0 < A) (hbox : ∀ z ∈ E, T.radius z ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E) :
    q * T.length / (2 * A) ≤ volume.real (Prod.fst '' E) := by
  have hw := T.width_pos
  have hstrip : ∀ z ∈ E, |z.2 - T.slope * z.1 - (T.y - T.slope * T.x)| ≤ A * T.width := by
    intro z hz
    have htrans : |T.transverse z| ≤ A := by
      have hh := hbox z hz
      unfold radius at hh
      linarith [abs_nonneg (T.horizontal z)]
    have heq : z.2 - T.slope * z.1 - (T.y - T.slope * T.x) =
        T.width * T.transverse z := by
      unfold transverse
      field_simp [T.width_pos.ne']
      ring
    rw [heq, abs_mul, abs_of_pos T.width_pos]
    nlinarith
  have hproj := projection_measure_bound E hE (mul_nonneg hA.le hw.le) hstrip
  apply (div_le_iff₀ (mul_pos (by norm_num) hA)).2
  nlinarith

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_WitnessLineAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact transferred witness gives the required popular line bin. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem measurableSet_lineBinSet (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    (s : ℝ) (z : ℝ × ℝ) (bin : Set ℝ) (hbin : MeasurableSet bin) :
    MeasurableSet (lineBinSet u s z bin) := by
  apply hbin.preimage
  exact hu.comp (by unfold linePoint; fun_prop)

namespace SlopeBox

/-- Turning the geometric transfer into an integral lower bound requires
only the measurable bin and the actual compact witness. -/
theorem witness_line_integral (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q : ℝ} (hA : 0 < A) (hbox : ∀ w ∈ E, T.radius w ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (s : ℝ) (z : ℝ × ℝ)
    (bin I : Set ℝ) (hbin : MeasurableSet bin) (hIfinite : volume I ≠ ∞)
    (hproj : ∀ w ∈ E, w.1 ∈ I)
    (htransfer : ∀ w ∈ E, u (referencePoint s z w) ∈ bin) :
    q * T.length / (2 * A) ≤
      ∫ x in I, (lineBinSet u s z bin).indicator (fun _ => (1 : ℝ)) x := by
  have hsubset : Prod.fst '' E ⊆ I ∩ lineBinSet u s z bin := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨hproj w hw, htransfer w hw⟩
  have hmeasure := measureReal_mono hsubset
    ((measure_mono (inter_subset_left : I ∩ lineBinSet u s z bin ⊆ I)).trans_lt
      (lt_top_iff_ne_top.mpr hIfinite)).ne
  have hbound := T.witness_projection_lower E hE hA hbox harea
  rw [setIntegral_indicator (measurableSet_lineBinSet u hu s z bin hbin), setIntegral_const]
  simpa only [smul_eq_mul, mul_one] using hbound.trans hmeasure

/-- The popular-bin threshold is the witness fraction divided only by the
fixed geometric dilation factors. -/
theorem witness_line_average (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q P : ℝ} (hA : 0 < A) (hq : 0 ≤ q) (hP : 0 < P)
    (hbox : ∀ w ∈ E, T.radius w ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (s : ℝ) (z : ℝ × ℝ)
    (bin I : Set ℝ) (hbin : MeasurableSet bin) (hIfinite : volume I ≠ ∞)
    (hIpos : 0 < volume.real I) (hIlength : volume.real I ≤ P * T.length)
    (hproj : ∀ w ∈ E, w.1 ∈ I)
    (htransfer : ∀ w ∈ E, u (referencePoint s z w) ∈ bin) :
    q / (2 * A * P) ≤
      (∫ x in I, (lineBinSet u s z bin).indicator (fun _ => (1 : ℝ)) x) / volume.real I := by
  apply (le_div_iff₀ hIpos).2
  have hthreshold : 0 ≤ q / (2 * A * P) := by positivity
  calc
    _ ≤ (q / (2 * A * P)) * (P * T.length) :=
      mul_le_mul_of_nonneg_left hIlength hthreshold
    _ = q * T.length / (2 * A) := by field_simp
    _ ≤ _ := T.witness_line_integral E hE hA hbox harea u hu s z bin I hbin
      hIfinite hproj htransfer

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact subwitness used for measurable horizontal projections. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

/-- Inner regularity produces the compact witness with half the original
area, while preserving every pointwise witness condition by inclusion. -/
theorem exists_compact_half_witness (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hfinite : (volume.prod volume) E ≠ ∞) (hpos : 0 < (volume.prod volume).real E) :
    ∃ K ⊆ E, IsCompact K ∧ (volume.prod volume).real E / 2 ≤
      (volume.prod volume).real K := by
  have hr : ENNReal.ofReal ((volume.prod volume).real E / 2) < (volume.prod volume) E := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
  obtain ⟨K, hKE, hK, harea⟩ := hE.exists_lt_isCompact_of_ne_top hfinite hr
  refine ⟨K, hKE, hK, ?_⟩
  have hle := ENNReal.toReal_mono (hK.measure_lt_top.ne) harea.le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (volume.prod volume).real E / 2)] at hle
  exact hle

namespace SlopeBox

/-- Extract the compact subwitness needed by the line-average argument from
the original measurable popularity witness. -/
theorem exists_compact_popularity_witness (T : SlopeBox) (E : Set (ℝ × ℝ))
    (hE : MeasurableSet E) (hfinite : (volume.prod volume) E ≠ ∞) {q A : ℝ}
    (hq : 0 < q) (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (hbox : ∀ z ∈ E, T.radius z ≤ A) :
    ∃ K ⊆ E, IsCompact K ∧
      (q / 2) * T.length * T.width ≤ (volume.prod volume).real K ∧
      ∀ z ∈ K, T.radius z ≤ A := by
  have hlength := T.length_pos
  have hwidth := T.width_pos
  have hpos : 0 < (volume.prod volume).real E :=
    (mul_pos (mul_pos hq hlength) hwidth).trans_le harea
  obtain ⟨K, hKE, hK, hhalf⟩ := exists_compact_half_witness E hE hfinite hpos
  refine ⟨K, hKE, hK, ?_, fun z hz => hbox z (hKE hz)⟩
  linarith

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WitnessInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete interval carries each transferred compact witness. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

theorem horizontal_distance_le_radius (T : SlopeBox) (z : ℝ × ℝ) :
    |z.1 - T.x| ≤ T.radius z * T.length := by
  have hh : |T.horizontal z| ≤ T.radius z := by
    unfold radius
    exact le_add_of_nonneg_right (abs_nonneg _)
  unfold horizontal at hh
  rw [abs_div, abs_of_pos T.length_pos] at hh
  exact (div_le_iff₀ T.length_pos).mp hh

theorem mem_witnessInterval (T : SlopeBox) {P : ℝ} {z : ℝ × ℝ}
    (hz : T.radius z ≤ P) : z.1 ∈ T.witnessInterval P := by
  have h := (T.horizontal_distance_le_radius z).trans
    (mul_le_mul_of_nonneg_right hz T.length_pos.le)
  have ha := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

theorem witnessInterval_length (T : SlopeBox) {P : ℝ} (hP : 0 ≤ P) :
    volume.real (T.witnessInterval P) = 2 * P * T.length := by
  rw [witnessInterval, Real.volume_real_Icc_of_le (by nlinarith [T.length_pos])]
  ring

/-- The witness produces the required average on a concrete interval that
also contains the evaluation point, with no further interval selection. -/
theorem witness_centered_line_average (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q P : ℝ} (hA : 0 < A) (hq : 0 ≤ q) (hP : 0 < P) (hAP : A ≤ P)
    (hbox : ∀ w ∈ E, T.radius w ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (s : ℝ) (z : ℝ × ℝ)
    (hz : T.radius z ≤ P) (bin : Set ℝ) (hbin : MeasurableSet bin)
    (htransfer : ∀ w ∈ E, u (referencePoint s z w) ∈ bin) :
    z.1 ∈ T.witnessInterval P ∧
      q / (4 * A * P) ≤
        (∫ x in T.witnessInterval P, (LipschitzHilbert.lineBinSet u s z bin).indicator
          (fun _ => (1 : ℝ)) x) / volume.real (T.witnessInterval P) := by
  refine ⟨T.mem_witnessInterval hz, ?_⟩
  have hl := T.length_pos
  have hlen := T.witnessInterval_length hP.le
  have havg := T.witness_line_average E hE hA hq (mul_pos (by norm_num : (0 : ℝ) < 2) hP)
    hbox harea u hu s z bin (T.witnessInterval P) hbin measure_Icc_lt_top.ne
    (by rw [hlen]; positivity) (by rw [hlen])
    (fun w hw => T.mem_witnessInterval ((hbox w hw).trans hAP)) htransfer
  convert havg using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Area-preserving reference-line coordinates for a top. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.SlopeBox

theorem referenceChart_measurePreserving (T : SlopeBox) :
    MeasurePreserving T.referenceChart (volume.prod volume) (volume.prod volume) := by
  change MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 + (T.y + T.slope * (z.1 - T.x)))) _ _
  exact (MeasurePreserving.id volume).skew_product (by fun_prop)
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (T.y + T.slope * (x - T.x)))

theorem referenceChart_image_measure (T : SlopeBox) (E : Set (ℝ × ℝ)) :
    (volume.prod volume) (T.referenceChart '' E) = (volume.prod volume) E := by
  have h := T.referenceChart_measurePreserving.measure_preimage_equiv (T.referenceChart '' E)
  rw [Set.preimage_image_eq E T.referenceChart.injective] at h
  exact h.symm

theorem referenceChart_inverse_transverse (T : SlopeBox) (z : ℝ × ℝ) :
    (T.referenceChart.symm z).2 = T.width * T.transverse z := by
  change z.2 - (T.y + T.slope * (z.1 - T.x)) = _
  unfold transverse
  field_simp [T.width_pos.ne']
  ring

/-- A horizontal line in reference coordinates is the actual line through
the physical evaluation point in the reference direction. -/
theorem referenceChart_linePoint (T : SlopeBox) (z : ℝ × ℝ) (x : ℝ) :
    T.referenceChart (x, (T.referenceChart.symm z).2) =
      LipschitzHilbert.linePoint T.slope z x := by
  ext
  · rfl
  · change (z.2 - (T.y + T.slope * (z.1 - T.x))) +
        (T.y + T.slope * (x - T.x)) = z.2 + T.slope * (x - z.1)
    ring

/-- Every significant point lies in the fixed reference rectangle. -/
theorem significant_mem_referenceRectangle (T : SlopeBox) {K : ℝ} {z : ℝ × ℝ}
    (hz : T.radius z ≤ K) : T.referenceChart.symm z ∈ T.referenceRectangle K := by
  refine ⟨?_, ?_⟩
  · change z.1 ∈ T.witnessInterval K
    exact T.mem_witnessInterval hz
  apply mem_Icc.mpr
  have hv : |T.transverse z| ≤ K := by
    unfold radius at hz
    linarith [abs_nonneg (T.horizontal z)]
  have habs : |(T.referenceChart.symm z).2| ≤ K * T.width := by
    rw [T.referenceChart_inverse_transverse, abs_mul, abs_of_pos T.width_pos]
    nlinarith [T.width_pos]
  simpa only [neg_mul] using abs_le.mp habs

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SectionMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating a uniform real section-length bound in reference coordinates. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

theorem section_measure_bound (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (U V : Set ℝ) (hV : MeasurableSet V) (hUf : volume U ≠ ∞) (hVf : volume V ≠ ∞)
    (hsub : E ⊆ U ×ˢ V) {M : ℝ} (hM : 0 ≤ M)
    (hsections : ∀ y ∈ V, volume.real ((fun x => (x, y)) ⁻¹' E) ≤ M) :
    (volume.prod volume).real E ≤ M * volume.real V := by
  have hsectionSub (y : ℝ) : ((fun x => (x, y)) ⁻¹' E) ⊆ U :=
    fun x hx => (hsub hx).1
  have hsectionFinite (y : ℝ) : volume ((fun x => (x, y)) ⁻¹' E) ≠ ∞ :=
    measure_ne_top_of_subset (hsectionSub y) hUf
  have hpoint (y : ℝ) : volume ((fun x => (x, y)) ⁻¹' E) ≤
      V.indicator (fun _ => ENNReal.ofReal M) y := by
    by_cases hy : y ∈ V
    · rw [indicator_of_mem hy]
      exact (ENNReal.le_ofReal_iff_toReal_le (hsectionFinite y) hM).2 (hsections y hy)
    · rw [indicator_of_notMem hy]
      have heq : ((fun x => (x, y)) ⁻¹' E) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hy (hsub hx).2
      simp only [heq, measure_empty, le_refl]
  have hmeasure : (volume.prod volume) E ≤ ENNReal.ofReal M * volume V := by
    rw [Measure.prod_apply_symm hE]
    calc
      _ ≤ ∫⁻ y, V.indicator (fun _ => ENNReal.ofReal M) y := lintegral_mono hpoint
      _ = _ := by rw [lintegral_indicator hV, lintegral_const, Measure.restrict_apply_univ]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVf) hmeasure
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hreal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CarlesonSorting
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordering the moment tuples in the laminar counting lemma

Each tuple has a sorting permutation. Summing over all permutations and
then reindexing the tuple sum gives the factorial overcount in §6,
`count:moment`, including repeated occurrences and repeated intervals.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [Fintype ι] [LinearOrder α]

omit [Fintype ι] in
theorem tuple_comp_perm_bijective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (fun a : Fin n → ι => a ∘ σ) := by
  constructor
  · intro a b hab
    funext i
    have h := congrFun hab (σ.symm i)
    simpa only [Function.comp_apply, σ.apply_symm_apply] using h
  · intro a
    refine ⟨a ∘ σ.symm, ?_⟩
    funext i
    simp only [Function.comp_apply, σ.symm_apply_apply]

/-- A nonnegative permutation-invariant tuple weight loses at most `n!`
when the tuple sum is restricted to one monotone ordering. -/
theorem sum_tuple_le_factorial_sum_sorted (rank : ι → α) (n : ℕ)
    (w : (Fin n → ι) → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hperm : ∀ (a : Fin n → ι) (σ : Equiv.Perm (Fin n)), w (a ∘ σ) = w a) :
    (∑ a : Fin n → ι, w a) ≤
      (n.factorial : ℝ) * ∑ a : Fin n → ι, if Monotone (rank ∘ a) then w a else 0 := by
  classical
  have hpoint (a : Fin n → ι) : w a ≤
      ∑ σ : Equiv.Perm (Fin n), if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 := by
    let σ := Tuple.sort (rank ∘ a)
    have hsorted : Monotone (rank ∘ (a ∘ σ)) := Tuple.monotone_sort (rank ∘ a)
    calc
      w a = if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 := by
        rw [ite_eq_left hsorted, hperm]
      _ ≤ _ := Finset.single_le_sum (a := σ) (f := fun τ : Equiv.Perm (Fin n) =>
          if Monotone (rank ∘ (a ∘ τ)) then w (a ∘ τ) else 0) (fun τ _ => by
          split_ifs
          · exact hw _
          · exact le_rfl)
        (Finset.mem_univ σ)
  calc
    (∑ a : Fin n → ι, w a) ≤ ∑ a : Fin n → ι,
        ∑ σ : Equiv.Perm (Fin n), if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ a : Fin n → ι,
        if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 := Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm (Fin n), ∑ a : Fin n → ι,
        if Monotone (rank ∘ a) then w a else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Fintype.sum_bijective _ (tuple_comp_perm_bijective σ) _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LaminarChains
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Iterated Carleson sums for a finite laminar family

The family is indexed by occurrences, so equal geometric intervals from
different bins retain their multiplicity. Iterating the actual Carleson
mass bound controls every non-strict nested-chain sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

omit [Fintype ι] in
theorem laminarChainWeight_nonneg (Q : ι → Set X) (μ : Measure X)
    (n : ℕ) (P : Set X) (a : Fin n → ι) : 0 ≤ laminarChainWeight Q μ n P a := by
  induction n generalizing P with
  | zero => exact measureReal_nonneg
  | succ n ih =>
    simp only [laminarChainWeight]
    split_ifs
    · exact ih _ _
    · exact le_rfl

theorem sum_laminarChainWeight_succ (Q : ι → Set X) (μ : Measure X)
    (n : ℕ) (P : Set X) :
    (∑ a : Fin (n + 1) → ι, laminarChainWeight Q μ (n + 1) P a) =
      ∑ i : ι, if Q i ⊆ P then ∑ a : Fin n → ι, laminarChainWeight Q μ n (Q i) a else 0 := by
  trans ∑ p : ι × (Fin n → ι),
    if Q p.1 ⊆ P then laminarChainWeight Q μ n (Q p.1) p.2 else 0
  · exact Fintype.sum_equiv (tupleHeadTailEquiv n) _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- The second inequality of `count:moment`, with repeated intervals allowed. -/
theorem sum_laminarChainWeight_le (Q : ι → Set X) (μ : Measure X) (P₀ : Set X)
    {A : ℝ} (hA : 0 ≤ A)
    (hcarleson : ∀ P, P = P₀ ∨ P ∈ Set.range Q →
      (∑ i, if Q i ⊆ P then μ.real (Q i) else 0) ≤ A * μ.real P)
    (n : ℕ) {P : Set X} (hP : P = P₀ ∨ P ∈ Set.range Q) :
    (∑ a : Fin n → ι, laminarChainWeight Q μ n P a) ≤ A ^ n * μ.real P := by
  induction n generalizing P with
  | zero => simp [laminarChainWeight]
  | succ n ih =>
    rw [sum_laminarChainWeight_succ]
    calc
      (∑ i, if Q i ⊆ P then ∑ a : Fin n → ι, laminarChainWeight Q μ n (Q i) a else 0) ≤
          ∑ i, if Q i ⊆ P then A ^ n * μ.real (Q i) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact ih (Or.inr ⟨i, rfl⟩)
        · exact le_rfl
      _ = A ^ n * ∑ i, if Q i ⊆ P then μ.real (Q i) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ ≤ A ^ n * (A * μ.real P) :=
        mul_le_mul_of_nonneg_left (hcarleson P hP) (pow_nonneg hA n)
      _ = A ^ (n + 1) * μ.real P := by rw [pow_succ]; ring

omit [Fintype ι] [MeasurableSpace X] in
theorem tupleIntersection_succ (Q : ι → Set X) {n : ℕ} (P : Set X)
    (a : Fin (n + 1) → ι) (hhead : Q (a 0) ⊆ P) :
    tupleIntersection Q P a = tupleIntersection Q (Q (a 0)) (fun j => a j.succ) := by
  ext x
  simp only [tupleIntersection, Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_succ]
  exact ⟨fun hx => ⟨hx.2.1, hx.2.2⟩,
    fun hx => ⟨hhead hx.1, hx.1, hx.2⟩⟩

omit [Fintype ι] in
theorem laminarChainWeight_eq_intersection (Q : ι → Set X) (μ : Measure X)
    (n : ℕ) (P : Set X) (a : Fin n → ι)
    (hsub : ∀ j, Q (a j) ⊆ P)
    (hnested : ∀ i j, i ≤ j → Q (a j) ⊆ Q (a i)) :
    laminarChainWeight Q μ n P a = μ.real (tupleIntersection Q P a) := by
  induction n generalizing P with
  | zero => simp [laminarChainWeight, tupleIntersection]
  | succ n ih =>
    rw [laminarChainWeight, ite_eq_left (hsub 0), tupleIntersection_succ Q P a (hsub 0)]
    apply ih
    · intro j
      exact hnested 0 j.succ (Fin.zero_le _)
    · intro i j hij
      exact hnested i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)

omit [Fintype ι] in
/-- Monotonicity of the scale rank turns every nonempty intersection into
an actual nested chain; empty intersections contribute zero. -/
theorem sorted_intersection_mass_le_chain (Q : ι → Set X) (μ : Measure X)
    (rank : ι → ℤ)
    (horder : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (n : ℕ) (P : Set X) (a : Fin n → ι) (hsub : ∀ j, Q (a j) ⊆ P)
    (hsorted : Antitone (rank ∘ a)) :
    μ.real (tupleIntersection Q P a) ≤ laminarChainWeight Q μ n P a := by
  by_cases hnonempty : (tupleIntersection Q P a).Nonempty
  · obtain ⟨x, hx⟩ := hnonempty
    have hnested : ∀ i j, i ≤ j → Q (a j) ⊆ Q (a i) := by
      intro i j hij
      apply horder _ _ (hsorted hij)
      exact ⟨x, Set.mem_iInter.mp hx.2 i, Set.mem_iInter.mp hx.2 j⟩
    rw [laminarChainWeight_eq_intersection Q μ n P a hsub hnested]
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, measureReal_empty]
    exact laminarChainWeight_nonneg Q μ n P a

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LaminarCarleson
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial moments of a finite laminar count

This proves equation `count:moment` of §6. The hypotheses are the actual
Carleson mass bound on the root and selected intervals and the geometric
ordering of intersecting intervals by their scale.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

theorem measurable_laminarCount (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) :
    Measurable (laminarCount Q) := by
  unfold laminarCount
  exact Finset.measurable_sum _ fun i _ => measurable_one.indicator (hQ i)

omit [MeasurableSpace X] in
theorem laminarCount_nonneg (Q : ι → Set X) (x : X) : 0 ≤ laminarCount Q x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [MeasurableSpace X] in
theorem laminarCount_le_card (Q : ι → Set X) (x : X) :
    laminarCount Q x ≤ (Fintype.card ι : ℝ) := by
  calc
    laminarCount Q x ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]
    _ = _ := by simp

omit [Fintype ι] [MeasurableSpace X] in
theorem tupleIntersection_comp_perm (Q : ι → Set X) {n : ℕ} (P : Set X)
    (a : Fin n → ι) (σ : Equiv.Perm (Fin n)) :
    tupleIntersection Q P (a ∘ σ) = tupleIntersection Q P a := by
  ext x
  simp only [tupleIntersection, Set.mem_inter_iff, Set.mem_iInter, Function.comp_apply]
  constructor
  · intro hx
    refine ⟨hx.1, fun j => ?_⟩
    simpa only [σ.apply_symm_apply] using hx.2 (σ.symm j)
  · intro hx
    exact ⟨hx.1, fun j => hx.2 (σ j)⟩

omit [Fintype ι] [MeasurableSpace X] in
theorem product_indicators_eq_tuple_indicator (Q : ι → Set X) {n : ℕ} (a : Fin n → ι) :
    (fun x => ∏ j, (Q (a j)).indicator (1 : X → ℝ) x) =
      (⋂ j, Q (a j)).indicator 1 := by
  funext x
  simpa using
    prod_indicator_apply Finset.univ (fun j => Q (a j)) (fun _ => (1 : X → ℝ)) x

theorem integral_laminarCount_pow (Q : ι → Set X) (μ : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i)) {P : Set X} (hPfinite : μ P ≠ ⊤) (n : ℕ) :
    (∫ x in P, laminarCount Q x ^ n ∂μ) =
      ∑ a : Fin n → ι, μ.real (tupleIntersection Q P a) := by
  have : IsFiniteMeasure (μ.restrict P) := isFiniteMeasure_restrict.mpr hPfinite
  have hmeas (a : Fin n → ι) : MeasurableSet (⋂ j, Q (a j)) := MeasurableSet.iInter (fun _ => hQ _)
  have hint (a : Fin n → ι) :
      Integrable (fun x => ∏ j, (Q (a j)).indicator (1 : X → ℝ) x) (μ.restrict P) := by
    rw [product_indicators_eq_tuple_indicator]
    exact (integrable_const (1 : ℝ)).indicator (hmeas a)
  simp only [laminarCount, Fintype.sum_pow]
  rw [integral_finsetSum _ (fun a _ => hint a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [product_indicators_eq_tuple_indicator, integral_indicator_one (hmeas a),
    measureReal_restrict_apply (hmeas a)]
  simp only [tupleIntersection, Set.inter_comm]

/-- The finite laminar Carleson moment bound, with exact factorial constant. -/
theorem laminar_count_moment (Q : ι → Set X) (μ : Measure X) (rank : ι → ℤ)
    (hQ : ∀ i, MeasurableSet (Q i)) {P₀ : Set X} (hPfinite : μ P₀ ≠ ⊤)
    (hsub : ∀ i, Q i ⊆ P₀)
    (horder : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    {A : ℝ} (hA : 0 ≤ A)
    (hcarleson : ∀ P, P = P₀ ∨ P ∈ Set.range Q →
      (∑ i, if Q i ⊆ P then μ.real (Q i) else 0) ≤ A * μ.real P)
    (n : ℕ) :
    (∫ x in P₀, laminarCount Q x ^ n ∂μ) ≤
      (n.factorial : ℝ) * A ^ n * μ.real P₀ := by
  rw [integral_laminarCount_pow Q μ hQ hPfinite]
  have hsort := sum_tuple_le_factorial_sum_sorted (fun i => -rank i) n
    (fun a => μ.real (tupleIntersection Q P₀ a)) (fun _ => measureReal_nonneg)
    (fun a σ => congrArg (μ.real) (tupleIntersection_comp_perm Q P₀ a σ))
  apply hsort.trans
  calc
    (n.factorial : ℝ) * ∑ a : Fin n → ι,
        (if Monotone (fun j => -rank (a j)) then μ.real (tupleIntersection Q P₀ a) else 0) ≤
      (n.factorial : ℝ) * ∑ a : Fin n → ι, laminarChainWeight Q μ n P₀ a := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro a _
      split_ifs with hs
      · have hs' : Antitone (rank ∘ a) := by
          intro i j hij
          have hh := hs hij
          exact neg_le_neg_iff.mp hh
        exact sorted_intersection_mass_le_chain Q μ rank horder n P₀ a (fun j => hsub (a j)) hs'
      · exact laminarChainWeight_nonneg Q μ n P₀ a
    _ ≤ (n.factorial : ℝ) * (A ^ n * μ.real P₀) :=
      mul_le_mul_of_nonneg_left (sum_laminarChainWeight_le Q μ P₀ hA hcarleson n (Or.inl rfl))
        (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CarlesonExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From factorial counting moments to an exponential tail

For a finite count the exponential series can be integrated using a
constant summable majorant. The exact factorial moment bound therefore
gives exponential average at most two and the required Markov tail.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

theorem factorial_moments_exponential_bound (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hmoment : ∀ n : ℕ, (∫ x, f x ^ n ∂μ) ≤ (n.factorial : ℝ) * A ^ n * μ.real Set.univ) :
    Integrable (fun x => Real.exp (f x / (2 * A))) μ ∧
      (∫ x, Real.exp (f x / (2 * A)) ∂μ) ≤ 2 * μ.real Set.univ := by
  let F : ℕ → X → ℝ := fun n x => (f x / (2 * A)) ^ n / (n.factorial : ℝ)
  let bound : ℕ → ℝ := fun n => (B / (2 * A)) ^ n / (n.factorial : ℝ)
  have hden : 0 < 2 * A := by positivity
  have hbound0 : ∀ n, 0 ≤ bound n := fun n => by dsimp [bound]; positivity
  have hFbound (n : ℕ) (x : X) : ‖F n x‖ ≤ bound n := by
    have hfx0 := hf0 x
    have hF0 : 0 ≤ F n x := by dsimp [F]; positivity
    rw [Real.norm_of_nonneg hF0]
    dsimp [F, bound]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (div_nonneg hfx0 hden.le)
      (div_le_div_of_nonneg_right (hfB x) hden.le) n
  have hFb (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact ((hf.div_const _).pow_const n |>.div_const _).aestronglyMeasurable
  have hsum_bound : Summable bound := NormedSpace.expSeries_div_summable _
  have hseries (x : X) : HasSum (fun n => F n x) (Real.exp (f x / (2 * A))) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (f x / (2 * A))
  have hsum := hasSum_integral_of_dominated_convergence (μ := μ)
    (fun n _ => bound n) hFb (fun n => Filter.Eventually.of_forall (hFbound n))
    (Filter.Eventually.of_forall fun _ => hsum_bound) (integrable_const _)
    (Filter.Eventually.of_forall hseries)
  have hint : Integrable (fun x => Real.exp (f x / (2 * A))) μ := by
    apply Integrable.of_bound ((hf.div_const _).exp.aestronglyMeasurable)
      (Real.exp (B / (2 * A)))
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (hfB x) hden.le
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) ≤ (1 / 2 : ℝ) ^ n * μ.real Set.univ := by
    have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hFn : F n = fun x => f x ^ n / ((2 * A) ^ n * (n.factorial : ℝ)) := by
      funext x
      dsimp [F]
      rw [div_pow, div_div]
    rw [hFn, integral_div]
    apply (div_le_iff₀ (mul_pos (pow_pos hden n) hfact)).2
    convert hmoment n using 1
    all_goals try with_reducible_and_instances rfl
    rw [mul_pow, div_pow]
    field_simp
    ring
  have hgeom : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * μ.real Set.univ)
      (2 * μ.real Set.univ) := by
    convert (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right
      (μ.real Set.univ) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  refine ⟨hint, ?_⟩
  rw [← hsum.tsum_eq, ← hgeom.tsum_eq]
  exact Summable.tsum_le_tsum hterm hsum.summable hgeom.summable

theorem exponential_moment_tail (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) {A : ℝ} (hA : 0 < A)
    (hint : Integrable (fun x => Real.exp (f x / (2 * A))) μ)
    (haverage : (∫ x, Real.exp (f x / (2 * A)) ∂μ) ≤ 2 * μ.real Set.univ)
    (lambda : ℝ) :
    μ.real {x | lambda < f x} ≤ 2 * μ.real Set.univ * Real.exp (-lambda / (2 * A)) := by
  have hden : 0 < 2 * A := by positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (f x / (2 * A))).le)
    hint (Real.exp (lambda / (2 * A)))
  have hsubset : {x | lambda < f x} ⊆
      {x | Real.exp (lambda / (2 * A)) ≤ Real.exp (f x / (2 * A))} := by
    intro x hx
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx.le hden.le)
  have hmono := measureReal_mono (μ := μ) hsubset
  have hle : μ.real {x | lambda < f x} ≤
      (2 * μ.real Set.univ) / Real.exp (lambda / (2 * A)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    nlinarith [mul_le_mul_of_nonneg_left hmono (Real.exp_pos (lambda / (2 * A))).le]
  convert hle using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv, neg_mul, Real.exp_neg]

/-- Exact exponential tail for the finite occurrence count in one root. -/
theorem laminar_count_exponential_tail {ι : Type*} [Fintype ι]
    (Q : ι → Set X) (μ : Measure X) (rank : ι → ℤ)
    (hQ : ∀ i, MeasurableSet (Q i)) {P₀ : Set X} (hPfinite : μ P₀ ≠ ⊤)
    (hsub : ∀ i, Q i ⊆ P₀)
    (horder : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    {A : ℝ} (hA : 0 < A)
    (hcarleson : ∀ P, P = P₀ ∨ P ∈ Set.range Q →
      (∑ i, if Q i ⊆ P then μ.real (Q i) else 0) ≤ A * μ.real P)
    (lambda : ℝ) :
    μ.real ({x | lambda < laminarCount Q x} ∩ P₀) ≤
      2 * μ.real P₀ * Real.exp (-lambda / (2 * A)) := by
  have : IsFiniteMeasure (μ.restrict P₀) := isFiniteMeasure_restrict.mpr hPfinite
  have hm (n : ℕ) : (∫ x, laminarCount Q x ^ n ∂μ.restrict P₀) ≤
      (n.factorial : ℝ) * A ^ n * (μ.restrict P₀).real Set.univ := by
    simpa only [measureReal_restrict_apply_univ] using
      laminar_count_moment Q μ rank hQ hPfinite hsub horder hA.le hcarleson n
  obtain ⟨hint, haverage⟩ := factorial_moments_exponential_bound (μ.restrict P₀)
    (laminarCount Q) (measurable_laminarCount Q hQ) hA
    (Nat.cast_nonneg (Fintype.card ι)) (laminarCount_nonneg Q) (laminarCount_le_card Q) hm
  have htail := exponential_moment_tail (μ.restrict P₀) (laminarCount Q) hA hint haverage lambda
  simpa only [measureReal_restrict_apply (measurableSet_lt measurable_const
    (measurable_laminarCount Q hQ)), measureReal_restrict_apply_univ] using htail

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountableCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable exhaustion of the Carleson tail

The count is an actual ENNReal sum over occurrences. Every finite subset
has the same exponential tail bound, so continuity from below gives that
bound for the full count without requiring a choice of enumeration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

theorem measurable_occurrenceCount (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) :
    Measurable (occurrenceCount Q) :=
  Measurable.tsum fun i => measurable_one.indicator (hQ i)

omit [Countable ι] in
theorem measurable_finiteOccurrenceCount (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i))
    (s : Finset ι) : Measurable (finiteOccurrenceCount Q s) :=
  Finset.measurable_sum s fun i _ => measurable_one.indicator (hQ i)

omit [Countable ι] [MeasurableSpace X] in
theorem finiteOccurrenceCount_mono (Q : ι → Set X) {s t : Finset ι} (hst : s ⊆ t) (x : X) :
    finiteOccurrenceCount Q s x ≤ finiteOccurrenceCount Q t x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hst
  intro i _ _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [Countable ι] [MeasurableSpace X] in
theorem ofReal_finiteOccurrenceCount (Q : ι → Set X) (s : Finset ι) (x : X) :
    ENNReal.ofReal (finiteOccurrenceCount Q s x) =
      ∑ i ∈ s, (Q i).indicator (1 : X → ℝ≥0∞) x := by
  unfold finiteOccurrenceCount
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx])]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [Countable ι] [MeasurableSpace X] in
theorem occurrenceCount_superlevel_eq_iUnion (Q : ι → Set X) {lambda : ℝ}
    (hlambda : 0 ≤ lambda) :
    {x | ENNReal.ofReal lambda < occurrenceCount Q x} =
      ⋃ s : Finset ι, {x | lambda < finiteOccurrenceCount Q s x} := by
  ext x
  simp only [Set.mem_ofPred_eq, occurrenceCount, ENNReal.tsum_eq_iSup_sum, lt_iSup_iff,
    Set.mem_iUnion]
  apply exists_congr
  intro s
  rw [← ofReal_finiteOccurrenceCount, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlambda]

/-- Uniform bounds on every finite subcount pass to the actual countable
sum. This is the monotone-convergence step in `count:line-lemma`. -/
theorem occurrenceCount_tail_of_finite (Q : ι → Set X) (μ : Measure X) [IsFiniteMeasure μ]
    {lambda B : ℝ} (hlambda : 0 ≤ lambda) (hB : 0 ≤ B)
    (hfinite : ∀ s : Finset ι, μ.real {x | lambda < finiteOccurrenceCount Q s x} ≤ B) :
    μ.real {x | ENNReal.ofReal lambda < occurrenceCount Q x} ≤ B := by
  rw [occurrenceCount_superlevel_eq_iUnion Q hlambda]
  have hdir : Directed (· ⊆ ·) (fun s : Finset ι => {x | lambda < finiteOccurrenceCount Q s x}) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x hx
      exact hx.trans_le (finiteOccurrenceCount_mono Q Finset.subset_union_left x)
    · intro x hx
      exact hx.trans_le (finiteOccurrenceCount_mono Q Finset.subset_union_right x)
  apply ENNReal.toReal_le_of_le_ofReal hB
  rw [hdir.measure_iUnion]
  apply iSup_le
  intro s
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hB).2 (hfinite s)

/-- The same exhaustion bound on a finite-measure root, even when the
ambient measure is infinite, as for Lebesgue measure on the line. -/
theorem occurrenceCount_root_tail_of_finite (Q : ι → Set X) (μ : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i)) {P : Set X} (hPfinite : μ P ≠ ⊤)
    {lambda B : ℝ} (hlambda : 0 ≤ lambda) (hB : 0 ≤ B)
    (hfinite : ∀ s : Finset ι,
      μ.real ({x | lambda < finiteOccurrenceCount Q s x} ∩ P) ≤ B) :
    μ.real ({x | ENNReal.ofReal lambda < occurrenceCount Q x} ∩ P) ≤ B := by
  have : IsFiniteMeasure (μ.restrict P) := isFiniteMeasure_restrict.mpr hPfinite
  have h := occurrenceCount_tail_of_finite Q (μ.restrict P) hlambda hB (fun s => by
    simpa only [measureReal_restrict_apply (measurableSet_lt measurable_const
      (measurable_finiteOccurrenceCount Q hQ s))] using hfinite s)
  simpa only [measureReal_restrict_apply (measurableSet_lt measurable_const
    (measurable_occurrenceCount Q hQ))] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only a controlled total length of root cells meets a bounded interval. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.DyadicLineGrid

theorem index_mono (q k : ℤ) : Monotone (index q k) := by
  intro a b hab
  apply Int.floor_mono
  exact sub_le_sub_right (div_le_div_of_nonneg_right hab (scale_pos k).le) _

theorem mem_rootBand_of_mem_interval {q k : ℤ} {a b x : ℝ} (hx : x ∈ Icc a b) :
    index q k x ∈ rootBand q k a b := by
  exact Finset.mem_Icc.mpr ⟨index_mono q k hx.1, index_mono q k hx.2⟩

theorem interval_subset_rootBand (q k : ℤ) (a b : ℝ) :
    Icc a b ⊆ ⋃ j ∈ rootBand q k a b, cell q k j := by
  intro x hx
  exact mem_iUnion.mpr ⟨index q k x, mem_iUnion.mpr
    ⟨mem_rootBand_of_mem_interval hx, mem_index_cell q k x⟩⟩

/-- The roots meeting a bounded interval have total length at most the
interval length plus two root lengths. -/
theorem rootBand_total_length (q k : ℤ) {a b : ℝ} (hab : a ≤ b) :
    (∑ j ∈ rootBand q k a b, volume.real (cell q k j)) ≤ b - a + 2 * scale k := by
  have hidx := index_mono q k hab
  have hcardZ : ((rootBand q k a b).card : ℤ) = index q k b + 1 - index q k a :=
    Int.card_Icc_of_le _ _ (by omega)
  have hcard : ((rootBand q k a b).card : ℝ) =
      (index q k b : ℝ) + 1 - index q k a := by exact_mod_cast hcardZ
  simp only [cell_length, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  have ha := mem_index_cell q k a
  have hb := mem_index_cell q k b
  change left q k (index q k a) ≤ a ∧ a < left q k (index q k a + 1) at ha
  change left q k (index q k b) ≤ b ∧ b < left q k (index q k b + 1) at hb
  unfold left at ha hb
  push_cast at ha hb
  nlinarith

/-- A largest scale exists within a factor two of any positive requested
length. Applied to `6H`, it gives exactly the source range `[6H,12H)`. -/
theorem exists_root_scale {H : ℝ} (hH : 0 < H) :
    ∃ k : ℤ, 6 * H ≤ scale k ∧ scale k < 12 * H := by
  obtain ⟨n, hn0, hn1⟩ := exists_mem_Ico_zpow
    (show (0 : ℝ) < 6 * H by positivity) (by norm_num : (1 : ℝ) < 2)
  by_cases heq : scale n = 6 * H
  · exact ⟨n, heq.ge, by rw [heq]; linarith⟩
  · refine ⟨n + 1, ?_, ?_⟩
    · exact le_of_lt hn1
    · rw [scale_succ]
      change scale n ≤ 6 * H at hn0
      have hlt := lt_of_le_of_ne hn0 heq
      linarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RootTailGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gluing rootwise counting tails on a bounded interval

Finite root covers and their total lengths transfer a rootwise tail to
any bounded interval. The two shifted grids used by the covering lemma
then combine by an exact ENNReal pigeonhole inequality.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι X : Type*} [MeasurableSpace X]

theorem measureReal_le_sum_of_finite_cover (μ : Measure X) (s : Finset ι)
    (Q : ι → Set X) {E : Set X} (hcover : E ⊆ ⋃ i ∈ s, Q i)
    (hfinite : ∀ i ∈ s, μ (Q i) ≠ ⊤) :
    μ.real E ≤ ∑ i ∈ s, μ.real (Q i) := by
  have hsum : (∑ i ∈ s, μ (Q i)) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun i hi => (hfinite i hi).lt_top)
  have hfin : μ (⋃ i ∈ s, Q i) ≠ ⊤ :=
    ((measure_biUnion_finset_le s Q).trans_lt hsum).ne
  exact (measureReal_mono hcover hfin).trans (measureReal_biUnion_finset_le s Q)

theorem finite_root_tail_gluing (μ : Measure X) (s : Finset ι) (Q : ι → Set X)
    {U E : Set X} (hcover : U ⊆ ⋃ i ∈ s, Q i)
    (hfinite : ∀ i ∈ s, μ (Q i) ≠ ⊤) {c : ℝ}
    (hroot : ∀ i ∈ s, μ.real (E ∩ Q i) ≤ c * μ.real (Q i)) :
    μ.real (E ∩ U) ≤ c * ∑ i ∈ s, μ.real (Q i) := by
  have hc : E ∩ U ⊆ ⋃ i ∈ s, E ∩ Q i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx.2)
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx.1, hxi⟩⟩
  calc
    μ.real (E ∩ U) ≤ ∑ i ∈ s, μ.real (E ∩ Q i) :=
      measureReal_le_sum_of_finite_cover μ s (fun i => E ∩ Q i) hc
        (fun i hi => measure_ne_top_of_subset Set.inter_subset_right (hfinite i hi))
    _ ≤ ∑ i ∈ s, c * μ.real (Q i) := Finset.sum_le_sum fun i hi => hroot i hi
    _ = _ := (Finset.mul_sum ..).symm

/-- Rootwise estimates combine with the actual floor-index root band. -/
theorem dyadic_root_tail_gluing (q k : ℤ) {a b : ℝ} (hab : a ≤ b)
    {E : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hroot : ∀ j ∈ DyadicLineGrid.rootBand q k a b,
      volume.real (E ∩ DyadicLineGrid.cell q k j) ≤
        c * volume.real (DyadicLineGrid.cell q k j)) :
    volume.real (E ∩ Set.Icc a b) ≤ c * (b - a + 2 * DyadicLineGrid.scale k) := by
  have h := finite_root_tail_gluing volume (DyadicLineGrid.rootBand q k a b)
    (DyadicLineGrid.cell q k) (DyadicLineGrid.interval_subset_rootBand q k a b)
    (fun j _ => by rw [DyadicLineGrid.cell, Real.volume_Ico]; exact ENNReal.ofReal_ne_top) hroot
  exact h.trans (mul_le_mul_of_nonneg_left (DyadicLineGrid.rootBand_total_length q k hab) hc)

omit [MeasurableSpace X] in
theorem ennreal_two_count_superlevel (f g : X → ℝ≥0∞) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    {x | ENNReal.ofReal lambda < f x + g x} ⊆
      {x | ENNReal.ofReal (lambda / 2) < f x} ∪
        {x | ENNReal.ofReal (lambda / 2) < g x} := by
  intro x hx
  by_contra h
  have h0 : f x ≤ ENNReal.ofReal (lambda / 2) := by
    exact le_of_not_gt (fun hf => h (Or.inl hf))
  have h1 : g x ≤ ENNReal.ofReal (lambda / 2) := by
    exact le_of_not_gt (fun hg => h (Or.inr hg))
  have hsum := add_le_add h0 h1
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  have heq : lambda / 2 + lambda / 2 = lambda := by ring
  rw [heq] at hsum
  exact not_lt_of_ge hsum hx

/-- Adding the counts from two grids costs a factor two in both the
front constant and the threshold. -/
theorem two_count_tail_gluing (μ : Measure X) {U : Set X} (hUfinite : μ U ≠ ⊤)
    (f g : X → ℝ≥0∞) {lambda B : ℝ} (hlambda : 0 ≤ lambda)
    (hf : μ.real ({x | ENNReal.ofReal (lambda / 2) < f x} ∩ U) ≤ B)
    (hg : μ.real ({x | ENNReal.ofReal (lambda / 2) < g x} ∩ U) ≤ B) :
    μ.real ({x | ENNReal.ofReal lambda < f x + g x} ∩ U) ≤ 2 * B := by
  have hcover : {x | ENNReal.ofReal lambda < f x + g x} ∩ U ⊆
      ({x | ENNReal.ofReal (lambda / 2) < f x} ∩ U) ∪
        ({x | ENNReal.ofReal (lambda / 2) < g x} ∩ U) := by
    intro x hx
    rcases ennreal_two_count_superlevel f g hlambda hx.1 with h | h
    · exact Or.inl ⟨h, hx.2⟩
    · exact Or.inr ⟨h, hx.2⟩
  have hfinite : μ (({x | ENNReal.ofReal (lambda / 2) < f x} ∩ U) ∪
      ({x | ENNReal.ofReal (lambda / 2) < g x} ∩ U)) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.union_subset Set.inter_subset_right Set.inter_subset_right) hUfinite
  have h := (measureReal_mono hcover hfinite).trans (measureReal_union_le _ _)
  linarith

/-- The rootwise Carleson tail on the two actual translated grids gives
the full bounded-interval tail, with the threshold loss made explicit. -/
theorem two_dyadic_root_exponential_tail (k : ℤ) {a b A lambda : ℝ}
    (hab : a ≤ b) (hA : 0 < A) (hlambda : 0 ≤ lambda)
    (count : ℤ → ℝ → ℝ≥0∞)
    (hroot : ∀ q ∈ ({0, 1} : Finset ℤ), ∀ j ∈ DyadicLineGrid.rootBand q k a b,
      ∀ t : ℝ, 0 ≤ t →
      volume.real ({x | ENNReal.ofReal t < count q x} ∩ DyadicLineGrid.cell q k j) ≤
        2 * volume.real (DyadicLineGrid.cell q k j) * Real.exp (-t / (2 * A))) :
    volume.real ({x | ENNReal.ofReal lambda < count 0 x + count 1 x} ∩ Set.Icc a b) ≤
      4 * (b - a + 2 * DyadicLineGrid.scale k) * Real.exp (-lambda / (4 * A)) := by
  have hexp : -(lambda / 2) / (2 * A) = -lambda / (4 * A) := by
    field_simp [ne_of_gt hA]
    ring
  have hq (q : ℤ) (hq : q ∈ ({0, 1} : Finset ℤ)) :
      volume.real ({x | ENNReal.ofReal (lambda / 2) < count q x} ∩ Set.Icc a b) ≤
        (2 * Real.exp (-lambda / (4 * A))) *
          (b - a + 2 * DyadicLineGrid.scale k) := by
    apply dyadic_root_tail_gluing q k hab (by positivity)
    intro j hj
    have hr := hroot q hq j hj (lambda / 2) (by positivity)
    rw [hexp] at hr
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := two_count_tail_gluing volume (by simp) (count 0) (count 1) hlambda
    (hq 0 (by simp)) (hq 1 (by simp))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- A root scale bounded by twelve times the allowed interval length
gives an absolute global constant. This applies to `exists_root_scale`. -/
theorem two_dyadic_root_exponential_tail_scale (k : ℤ) {a b A H lambda : ℝ}
    (hab : a ≤ b) (hA : 0 < A) (hlambda : 0 ≤ lambda)
    (hscale : DyadicLineGrid.scale k ≤ 12 * H)
    (count : ℤ → ℝ → ℝ≥0∞)
    (hroot : ∀ q ∈ ({0, 1} : Finset ℤ), ∀ j ∈ DyadicLineGrid.rootBand q k a b,
      ∀ t : ℝ, 0 ≤ t →
      volume.real ({x | ENNReal.ofReal t < count q x} ∩ DyadicLineGrid.cell q k j) ≤
        2 * volume.real (DyadicLineGrid.cell q k j) * Real.exp (-t / (2 * A))) :
    volume.real ({x | ENNReal.ofReal lambda < count 0 x + count 1 x} ∩ Set.Icc a b) ≤
      96 * (b - a + H) * Real.exp (-lambda / (4 * A)) := by
  refine (two_dyadic_root_exponential_tail k hab hA hlambda count hroot).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maximal bad intervals exist below a fixed largest dyadic scale. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

/-- Within one bin, distinct maximal bad intervals are disjoint. -/
theorem maximalBad_disjoint {q top k l i j : ℤ} {bad : ℤ → ℤ → Prop}
    (hi : MaximalBad q top bad k i) (hj : MaximalBad q top bad l j)
    (hne : (k, i) ≠ (l, j)) : Disjoint (cell q k i) (cell q l j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exact hi.2.2 l j hkl hj.1 (cell_subset_of_intersect hkl.le ⟨x, hxi, hxj⟩) hj.2.1
  · subst l
    have hij : i = j := (index_eq_of_mem hxi).symm.trans (index_eq_of_mem hxj)
    exact hne (by simp [hij])
  · exact hj.2.2 k i hlk hi.1 (cell_subset_of_intersect hlk.le ⟨x, hxj, hxi⟩) hi.2.1

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DyadicLineCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform interval cover by the nested one-third dyadic grids. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

/-- The elementary one-third covering step at a fixed scale. -/
theorem unit_interval_cover {a b δ : ℝ} (hδ0 : 1 / 3 ≤ δ) (hδ1 : δ ≤ 2 / 3)
    (hlen : b - a < 1 / 3) :
    (∃ j : ℤ, Icc a b ⊆ Ico (j : ℝ) (j + 1)) ∨
      ∃ j : ℤ, Icc a b ⊆ Ico ((j : ℝ) + δ) (j + 1 + δ) := by
  let n : ℤ := ⌊a⌋
  have hn0 : (n : ℝ) ≤ a := Int.floor_le a
  have hn1 : a < (n : ℝ) + 1 := Int.lt_floor_add_one a
  by_cases hb : b < (n : ℝ) + 1
  · left
    refine ⟨n, ?_⟩
    intro x hx
    exact ⟨hn0.trans hx.1, hx.2.trans_lt hb⟩
  · right
    refine ⟨n, ?_⟩
    intro x ⟨hxa, hxb⟩
    constructor <;> linarith [le_of_not_gt hb]

/-- Each interval shorter than one third of a grid cell fits in one cell of
the ordinary or alternating one-third grid. -/
theorem fixed_scale_interval_cover (k : ℤ) {a b : ℝ} (hlen : b - a < scale k / 3) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ j : ℤ, Icc a b ⊆ cell q k j := by
  have hs := scale_pos k
  have hnorm : b / scale k - a / scale k < 1 / 3 := by
    have hh : (b - a) / scale k < 1 / 3 := (div_lt_iff₀ hs).2 (by nlinarith)
    simpa only [sub_div] using hh
  have hsign : (k.negOnePow : ℤ) = 1 ∨ (k.negOnePow : ℤ) = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (Int.abs_negOnePow k)
  rcases hsign with hsign | hsign
  · obtain h | h := unit_interval_cover (δ := 1 / 3) (by norm_num) (by norm_num) hnorm
    · obtain ⟨j, hj⟩ := h
      refine ⟨0, by simp, j, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, mul_zero, Int.cast_zero, zero_div, add_zero]
      push_cast
      constructor <;> nlinarith
    · obtain ⟨j, hj⟩ := h
      refine ⟨1, by simp, j, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, hsign, mul_one, Int.cast_one]
      push_cast
      constructor <;> nlinarith
  · obtain h | h := unit_interval_cover (δ := 2 / 3) (by norm_num) (by norm_num) hnorm
    · obtain ⟨j, hj⟩ := h
      refine ⟨0, by simp, j, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, mul_zero, Int.cast_zero, zero_div, add_zero]
      push_cast
      constructor <;> nlinarith
    · obtain ⟨j, hj⟩ := h
      refine ⟨1, by simp, j + 1, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, hsign, mul_one, Int.cast_neg, Int.cast_one]
      push_cast
      constructor <;> nlinarith

/-- A positive-length interval is contained in a dyadic interval of length
at most six times its own, with one of two fixed nested grids. -/
theorem interval_cover {a b : ℝ} (hab : a < b) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ k j : ℤ,
      Icc a b ⊆ cell q k j ∧ scale k ≤ 6 * (b - a) := by
  obtain ⟨n, hn0, hn1⟩ := exists_mem_Ico_zpow
    (show (0 : ℝ) < 3 * (b - a) by linarith) (by norm_num : (1 : ℝ) < 2)
  have hlarge : b - a < scale (n + 1) / 3 := by
    change 3 * (b - a) < scale (n + 1) at hn1
    linarith
  obtain ⟨q, hq, j, hj⟩ := fixed_scale_interval_cover (n + 1) hlarge
  refine ⟨q, hq, n + 1, j, hj, ?_⟩
  change scale n ≤ 3 * (b - a) at hn0
  rw [scale_succ]
  linarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineBad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Popular intervals produce maximal bad intervals in two fixed grids. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.DyadicLineGrid

theorem scale_le_iff {k l : ℤ} : scale k ≤ scale l ↔ k ≤ l :=
  zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)

theorem integrableOn_of_unit_bound {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {S : Set ℝ} (hS : volume S ≠ ∞) :
    IntegrableOn f S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x).1] using (hbound x).2

/-- A popular interval fits in a bad dyadic interval, with only the factor-six
loss in the average and with the prescribed upper scale. -/
theorem popular_interval_has_bad {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b θ H : ℝ} {top : ℤ}
    (hab : a < b) (hθ : 0 ≤ θ) (hlen : b - a ≤ H) (htop : 6 * H ≤ scale top)
    (hpopular : θ * (b - a) ≤ ∫ x in Icc a b, f x) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ k j,
      k ≤ top ∧ Icc a b ⊆ cell q k j ∧ Bad q f (θ / 6) k j := by
  obtain ⟨q, hq, k, j, hcover, hsize⟩ := interval_cover hab
  have hk : k ≤ top := scale_le_iff.mp (hsize.trans ((mul_le_mul_of_nonneg_left hlen (by norm_num)).trans htop))
  have hint : IntegrableOn f (cell q k j) :=
    integrableOn_of_unit_bound hf hbound measure_Ico_lt_top.ne
  have hmono : (∫ x in Icc a b, f x) ≤ ∫ x in cell q k j, f x :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => (hbound x).1)
      (Filter.Eventually.of_forall fun _ hx => hcover hx)
  refine ⟨q, hq, k, j, hk, hcover, ?_⟩
  unfold Bad
  have hmul := mul_le_mul_of_nonneg_left hsize (div_nonneg hθ (by norm_num : (0 : ℝ) ≤ 6))
  nlinarith [hpopular.trans hmono]

/-- Hence every popular interval through a point is accounted for by a
maximal bad interval in one of the two fixed grids. -/
theorem popular_interval_has_maximalBad {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b θ H x : ℝ} {top : ℤ}
    (hab : a < b) (hθ : 0 ≤ θ) (hlen : b - a ≤ H) (htop : 6 * H ≤ scale top)
    (hx : x ∈ Icc a b) (hpopular : θ * (b - a) ≤ ∫ y in Icc a b, f y) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ k j,
      MaximalBad q top (Bad q f (θ / 6)) k j ∧ x ∈ cell q k j := by
  obtain ⟨q, hq, k, j, hk, hcover, hbad⟩ := popular_interval_has_bad hf hbound hab hθ hlen htop hpopular
  obtain ⟨l, i, hmax, hsub⟩ := exists_maximalBad hk hbad
  exact ⟨q, hq, l, i, hmax, hsub (hcover hx)⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A jointly measurable count of the actual maximal dyadic occurrences. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.DyadicLineGrid

variable {X B : Type*} [MeasurableSpace X]

theorem measurableSet_bad (f : X × ℝ → ℝ) (hf : Measurable f)
    (q : ℤ) (β : ℝ) (k j : ℤ) :
    MeasurableSet {p | Bad q (fun x => f (p, x)) β k j} := by
  exact measurableSet_le measurable_const
    (hf.stronglyMeasurable.integral_prod_right'.measurable)

theorem measurableSet_maximalBad (q top : ℤ) (bad : X → ℤ → ℤ → Prop)
    (hbad : ∀ k j, MeasurableSet {p | bad p k j}) (k j : ℤ) :
    MeasurableSet {p | MaximalBad q top (bad p) k j} := by
  by_cases hk : k ≤ top
  · have hforall : MeasurableSet {p | ∀ l i, k < l → l ≤ top →
        cell q k j ⊆ cell q l i → ¬bad p l i} := by
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro l
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      by_cases hkl : k < l
      · by_cases hlt : l ≤ top
        · by_cases hsub : cell q k j ⊆ cell q l i
          · simpa only [hkl, hlt, hsub, true_implies, ← compl_ofPred] using (hbad l i).compl
          · simpa only [hsub, false_implies, implies_true, ofPred_true] using MeasurableSet.univ (α := X)
        · simpa only [hlt, false_implies, implies_true, ofPred_true] using MeasurableSet.univ (α := X)
      · simpa only [hkl, false_implies, ofPred_true] using MeasurableSet.univ (α := X)
    simpa only [MaximalBad, hk, true_and, ofPred_and] using (hbad k j).inter hforall
  · simpa only [MaximalBad, hk, false_and, ofPred_false] using MeasurableSet.empty (α := X)

theorem measurableSet_selectedSet (f : B → X × ℝ → ℝ)
    (hf : ∀ b, Measurable (f b)) (top : ℤ) (β : ℝ) (a : Occurrence B) :
    MeasurableSet (selectedSet f top β a) := by
  by_cases hq : a.1 ∈ ({0, 1} : Finset ℤ)
  · have hm := measurableSet_maximalBad a.1 top
      (fun p => Bad a.1 (fun x => f a.2.1 (p, x)) β)
      (measurableSet_bad (f a.2.1) (hf a.2.1) a.1 β) a.2.2.1 a.2.2.2
    convert
      (hm.preimage measurable_fst).inter ((cell_measurable a.1 a.2.2.1 a.2.2.2).preimage measurable_snd)
      using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [selectedSet, hq, true_and, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  · simpa only [selectedSet, hq, false_and, ofPred_false] using MeasurableSet.empty (α := X × ℝ)

theorem measurable_selectedCount [Countable B] (f : B → X × ℝ → ℝ)
    (hf : ∀ b, Measurable (f b)) (top : ℤ) (β : ℝ) :
    Measurable (selectedCount f top β) := by
  apply Measurable.tsum
  intro a
  exact measurable_const.indicator (measurableSet_selectedSet f hf top β a)

/- Distinct popular bins contribute distinct occurrences to the one fixed
measurable count, even though their witnessing intervals are arbitrary. -/
omit [MeasurableSpace X] in
theorem card_le_selectedCount (f : B → X × ℝ → ℝ) (top : ℤ) (β : ℝ)
    (p : X × ℝ) (bins : Finset B)
    (hwitness : ∀ b ∈ bins, ∃ a : Occurrence B, a.2.1 = b ∧ p ∈ selectedSet f top β a) :
    (bins.card : ℝ≥0∞) ≤ selectedCount f top β p := by
  classical
  choose a ha using fun b : bins => hwitness b b.property
  have hinj : Function.Injective a := by
    intro b c hac
    apply Subtype.ext
    exact (ha b).1.symm.trans ((congrArg (fun z : Occurrence B => z.2.1) hac).trans (ha c).1)
  have hcomp := ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun z : Occurrence B => (selectedSet f top β z).indicator (1 : X × ℝ → ℝ≥0∞) p)
  have hval : ∀ b : bins, (selectedSet f top β (a b)).indicator (1 : X × ℝ → ℝ≥0∞) p = 1 :=
    fun b => Set.indicator_of_mem (ha b).2 _
  simpa only [hval, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one, selectedCount] using hcomp

/-- The one count dominates every finite family of distinct popular bins.
The intervals may be chosen separately for each bin and point. -/
theorem popular_bins_card_le_selectedCount (f : B → X × ℝ → ℝ)
    (hf : ∀ b, Measurable (f b))
    (hbound : ∀ b p, 0 ≤ f b p ∧ f b p ≤ 1)
    {θ H : ℝ} {top : ℤ} (hθ : 0 ≤ θ) (htop : 6 * H ≤ scale top)
    (p : X × ℝ) (bins : Finset B)
    (hpopular : ∀ b ∈ bins, ∃ a c : ℝ, a < c ∧ c - a ≤ H ∧ p.2 ∈ Icc a c ∧
      θ * (c - a) ≤ ∫ x in Icc a c, f b (p.1, x)) :
    (bins.card : ℝ≥0∞) ≤ selectedCount f top (θ / 6) p := by
  apply card_le_selectedCount
  intro b hb
  obtain ⟨a, c, hac, hlen, hx, havg⟩ := hpopular b hb
  have hmeas : Measurable (fun x => f b (p.1, x)) :=
    (hf b).comp (measurable_const.prodMk measurable_id)
  obtain ⟨q, hq, k, j, hmax, hcell⟩ := popular_interval_has_maximalBad hmeas
    (fun x => hbound b (p.1, x)) hac hθ hlen htop hx havg
  exact ⟨(q, b, k, j), rfl, hq, hmax, hcell⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BinCarleson
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Carleson mass bound from disjoint intervals within each bin. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι B X : Type*} [Fintype ι] [Fintype B]

/-- At a point, pairwise disjointness within each bin prevents that bin's
function from being counted more than once. -/
theorem sum_bin_indicators_le (Q : ι → Set X) (bin : ι → B) (f : B → X → ℝ)
    (hf : ∀ b x, 0 ≤ f b x)
    (hdisj : ∀ i j, i ≠ j → bin i = bin j → Disjoint (Q i) (Q j)) (x : X) :
    (∑ i, (Q i).indicator (f (bin i)) x) ≤ ∑ b, f b x := by
  classical
  let s := Finset.univ.filter (fun i => x ∈ Q i)
  have hinj : Set.InjOn bin (s : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj i j hne hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hsum : (∑ i, (Q i).indicator (f (bin i)) x) = ∑ i ∈ s, f (bin i) x := by
    simp only [s, Finset.sum_filter, Set.indicator_apply]
  rw [hsum]
  exact OAI.sum_le_sum_of_injOn bin hinj (by simp) (fun _ _ => le_rfl)
    (fun b _ _ => hf b x)

variable [MeasurableSpace X]

/-- The finite mass bound underlying the line counting lemma. Different
bins may select the same interval; disjointness is needed only within a bin. -/
theorem finite_bin_carleson (Q : ι → Set X) (bin : ι → B) (f : B → X → ℝ)
    (μ : Measure X) {P : Set X} (hP : MeasurableSet P) (hPfinite : μ P ≠ ∞)
    (hQ : ∀ i, MeasurableSet (Q i)) (hsub : ∀ i, Q i ⊆ P)
    (hf : ∀ b, IntegrableOn (f b) P μ) (hnonneg : ∀ b x, 0 ≤ f b x)
    (hdisj : ∀ i j, i ≠ j → bin i = bin j → Disjoint (Q i) (Q j))
    {β C : ℝ} (hβ : 0 < β) (hsum : ∀ x ∈ P, (∑ b, f b x) ≤ C)
    (hbad : ∀ i, β * μ.real (Q i) ≤ ∫ x in Q i, f (bin i) x ∂μ) :
    (∑ i, μ.real (Q i)) ≤ (C / β) * μ.real P := by
  have : IsFiniteMeasure (μ.restrict P) := isFiniteMeasure_restrict.mpr hPfinite
  have hind : ∀ i, Integrable (fun x => (Q i).indicator (f (bin i)) x) (μ.restrict P) :=
    fun i => (hf (bin i)).indicator (hQ i)
  have heq : (∑ i, ∫ x in Q i, f (bin i) x ∂μ) =
      ∫ x in P, ∑ i, (Q i).indicator (f (bin i)) x ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hind i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [setIntegral_indicator (hQ i), inter_eq_right.mpr (hsub i)]
  have hbound : β * (∑ i, μ.real (Q i)) ≤ C * μ.real P := by
    calc
      _ = ∑ i, β * μ.real (Q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i, ∫ x in Q i, f (bin i) x ∂μ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = _ := heq
      _ ≤ ∫ _ in P, C ∂μ := by
        apply setIntegral_mono_on (integrable_finsetSum _ (fun i _ => hind i))
          (integrable_const C) hP
        intro x hx
        exact (sum_bin_indicators_le Q bin f hnonneg hdisj x).trans (hsum x hx)
      _ = C * μ.real P := by simp [mul_comm]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hβ).2
  simpa only [mul_comm] using hbound

/-- The same estimate for an arbitrary bin type, using only a uniform bound
on its finite partial sums. -/
theorem finite_bin_carleson_of_finite_sums {B' : Type*}
    (Q : ι → Set X) (bin : ι → B') (f : B' → X → ℝ)
    (μ : Measure X) {P : Set X} (hP : MeasurableSet P) (hPfinite : μ P ≠ ∞)
    (hQ : ∀ i, MeasurableSet (Q i)) (hsub : ∀ i, Q i ⊆ P)
    (hf : ∀ b, IntegrableOn (f b) P μ) (hnonneg : ∀ b x, 0 ≤ f b x)
    (hdisj : ∀ i j, i ≠ j → bin i = bin j → Disjoint (Q i) (Q j))
    {β C : ℝ} (hβ : 0 < β) (hsum : ∀ s : Finset B', ∀ x ∈ P, (∑ b ∈ s, f b x) ≤ C)
    (hbad : ∀ i, β * μ.real (Q i) ≤ ∫ x in Q i, f (bin i) x ∂μ) :
    (∑ i, μ.real (Q i)) ≤ (C / β) * μ.real P := by
  classical
  let bins := Finset.univ.image bin
  let bin' (i : ι) : bins := ⟨bin i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  apply finite_bin_carleson Q bin' (fun b => f b.1) μ hP hPfinite hQ hsub
    (fun b => hf b.1) (fun b => hnonneg b.1)
  · intro i j hij hb
    exact hdisj i j hij (congrArg Subtype.val hb)
  · exact hβ
  · intro x hx
    calc
      _ = ∑ b ∈ bins, f b x := (Finset.sum_subtype bins (fun _ => Iff.rfl) (fun b => f b x)).symm
      _ ≤ C := hsum bins x hx
  · exact hbad

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineCarleson
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual maximal bad intervals satisfy the finite Carleson bound. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

theorem maximal_bad_carleson {ι B : Type*} [Fintype ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    {P : Set ℝ} (hP : MeasurableSet P) (hPfinite : volume P ≠ ∞)
    (hsub : ∀ i, cell q (level i) (pos i) ⊆ P) :
    (∑ i, volume.real (cell q (level i) (pos i))) ≤ (C / β) * volume.real P := by
  apply finite_bin_carleson_of_finite_sums (fun i => cell q (level i) (pos i)) bin f volume
    hP hPfinite (fun i => cell_measurable q (level i) (pos i)) hsub
    (fun b => integrableOn_of_unit_bound (hf b) (hbound b) hPfinite)
    (fun b x => (hbound b x).1)
  · intro i j hij hb
    apply maximalBad_disjoint (hmax i)
    · simpa only [← hb] using hmax j
    · intro hcoords
      exact hij (hunique i j hb (congrArg Prod.fst hcoords) (congrArg Prod.snd hcoords))
  · exact hβ
  · intro s x _
    exact hsum s x
  · intro i
    rw [cell_length]
    exact (hmax i).2.1

/-- Restricting a finite family of occurrences to any finite-measure test
set preserves the same Carleson constant. -/
theorem maximal_bad_carleson_restricted {ι B : Type*} [Fintype ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    {P : Set ℝ} (hP : MeasurableSet P) (hPfinite : volume P ≠ ∞) :
    (∑ i, if cell q (level i) (pos i) ⊆ P then volume.real (cell q (level i) (pos i)) else 0) ≤
      (C / β) * volume.real P := by
  classical
  let s := Finset.univ.filter (fun i => cell q (level i) (pos i) ⊆ P)
  have h := maximal_bad_carleson (ι := s) q top f (fun i => bin i.1)
    (fun i => level i.1) (fun i => pos i.1)
    (fun i j hb hl hp => Subtype.ext (hunique i.1 j.1 hb hl hp))
    hβ (fun i => hmax i.1) hf hbound hsum hP hPfinite
    (fun i => (Finset.mem_filter.mp i.property).2)
  have heq : (∑ i : s, volume.real (cell q (level i.1) (pos i.1))) =
      ∑ i ∈ s, volume.real (cell q (level i) (pos i)) :=
    (Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => volume.real (cell q (level i) (pos i)))).symm
  rw [heq] at h
  simpa only [s, Finset.sum_filter] using h

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineFiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exponential count bound for actual finite maximal dyadic families. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

theorem maximal_bad_finite_tail {ι B : Type*} [Fintype ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    (rootLevel rootPos : ℤ)
    (hsub : ∀ i, cell q (level i) (pos i) ⊆ cell q rootLevel rootPos)
    (lambda : ℝ) :
    volume.real ({x | lambda < laminarCount (fun i => cell q (level i) (pos i)) x} ∩
      cell q rootLevel rootPos) ≤
      2 * scale rootLevel * Real.exp (-lambda / (2 * (C / β))) := by
  have hcarleson : ∀ P, P = cell q rootLevel rootPos ∨
      P ∈ range (fun i => cell q (level i) (pos i)) →
      (∑ i, if cell q (level i) (pos i) ⊆ P then volume.real (cell q (level i) (pos i)) else 0) ≤
        (C / β) * volume.real P := by
    intro P hP
    have hPm : MeasurableSet P := by
      rcases hP with rfl | ⟨i, rfl⟩
      · exact cell_measurable q rootLevel rootPos
      · exact cell_measurable q (level i) (pos i)
    have hPf : volume P ≠ ∞ := by
      rcases hP with rfl | ⟨i, rfl⟩ <;> exact measure_Ico_lt_top.ne
    exact maximal_bad_carleson_restricted q top f bin level pos hunique hβ hmax hf hbound hsum hPm hPf
  have hc := laminar_count_exponential_tail (fun i => cell q (level i) (pos i)) volume level
    (fun i => cell_measurable q (level i) (pos i)) measure_Ico_lt_top.ne hsub
    (fun i j hji hmeet => cell_subset_of_intersect hji (by simpa only [inter_comm] using hmeet))
    (div_pos hC hβ) hcarleson lambda
  have hlen : volume.real (Ico (left q rootLevel rootPos) (left q rootLevel (rootPos + 1))) =
      scale rootLevel := cell_length q rootLevel rootPos
  rw [hlen] at hc
  exact hc

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineCountableTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform tails for countably many actual maximal dyadic occurrences. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

theorem maximal_bad_countable_tail {ι B : Type*} [Countable ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    (rootLevel rootPos : ℤ)
    (hsub : ∀ i, cell q (level i) (pos i) ⊆ cell q rootLevel rootPos)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    volume.real ({x | ENNReal.ofReal lambda < occurrenceCount (fun i => cell q (level i) (pos i)) x} ∩
      cell q rootLevel rootPos) ≤
      2 * scale rootLevel * Real.exp (-lambda / (2 * (C / β))) := by
  classical
  apply occurrenceCount_root_tail_of_finite _ volume
    (fun i => cell_measurable q (level i) (pos i)) measure_Ico_lt_top.ne hlambda
    (mul_nonneg (mul_nonneg (by norm_num) (scale_pos rootLevel).le) (Real.exp_pos _).le)
  intro s
  have ht := maximal_bad_finite_tail (ι := s) q top f (fun i => bin i.1)
    (fun i => level i.1) (fun i => pos i.1)
    (fun i j hb hl hp => Subtype.ext (hunique i.1 j.1 hb hl hp)) hβ hC
    (fun i => hmax i.1) hf hbound hsum rootLevel rootPos (fun i => hsub i.1) lambda
  have heq (x : ℝ) : laminarCount (fun i : s => cell q (level i.1) (pos i.1)) x =
      finiteOccurrenceCount (fun i => cell q (level i) (pos i)) s x := by
    exact (Finset.sum_subtype s (fun _ => Iff.rfl)
      (fun i => (cell q (level i) (pos i)).indicator (1 : ℝ → ℝ) x)).symm
  simp_rw [heq] at ht
  simpa only [cell] using ht

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineRootCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The count in one grid agrees on a root with the count of its selected descendants. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

theorem selectedCount_eq_gridCounts {B X : Type*} (f : B → X × ℝ → ℝ)
    (top : ℤ) (β : ℝ) (p : X × ℝ) :
    selectedCount f top β p =
      gridCount (fun b x => f b (p.1, x)) 0 top β p.2 +
        gridCount (fun b x => f b (p.1, x)) 1 top β p.2 := by
  classical
  unfold selectedCount
  rw [ENNReal.tsum_prod']
  have hterm (q : ℤ) :
      (∑' a : GridOccurrence B, (selectedSet f top β (q, a)).indicator 1 p) =
        if q ∈ ({0, 1} : Finset ℤ) then gridCount (fun b x => f b (p.1, x)) q top β p.2 else 0 := by
    by_cases hq : q ∈ ({0, 1} : Finset ℤ)
    · rw [ite_eq_left hq]
      unfold gridCount occurrenceCount
      apply tsum_congr
      intro a
      by_cases hm : MaximalBad q top (Bad q (fun x => f a.1 (p.1, x)) β) a.2.1 a.2.2
      · simp [selectedSet, maximalCell, hq, hm, indicator_apply]
      · simp [selectedSet, maximalCell, hq, hm]
    · rw [ite_eq_right hq]
      simp [selectedSet, hq]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ)) (fun q hq => by simp [hq])]
  simp

theorem gridCount_eq_rootCount {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ)
    (j : ℤ) {x : ℝ} (hx : x ∈ cell q top j) :
    gridCount f q top β x =
      occurrenceCount (fun a : RootOccurrence f q top β j => cell q a.1.2.1 a.1.2.2) x := by
  classical
  let g : GridOccurrence B → ℝ≥0∞ := fun a => (maximalCell f q top β a).indicator 1 x
  have hs : support g ⊆ {a | MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2 ∧
      cell q a.2.1 a.2.2 ⊆ cell q top j} := by
    intro a ha
    have ha0 : g a ≠ 0 := ha
    by_cases hm : MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2
    · have hax : x ∈ cell q a.2.1 a.2.2 := by
        by_contra hn
        simp only [g, maximalCell, ite_eq_left hm, indicator_of_notMem hn] at ha0
        exact ha0 rfl
      exact ⟨hm, cell_subset_of_intersect hm.1 ⟨x, hax, hx⟩⟩
    · simp only [g, maximalCell, ite_eq_right hm, indicator_empty] at ha0
      exact (ha0 rfl).elim
  have heq := tsum_subtype_eq_of_support_subset hs
  change (∑' a, g a) = _
  rw [← heq]
  apply tsum_congr
  intro a
  simp only [g, maximalCell, ite_eq_left a.property.1]

theorem gridCount_root_tail {B : Type*} [Countable B]
    (f : B → ℝ → ℝ) (q top : ℤ) {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    (j : ℤ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    volume.real ({x | ENNReal.ofReal lambda < gridCount f q top β x} ∩ cell q top j) ≤
      2 * scale top * Real.exp (-lambda / (2 * (C / β))) := by
  classical
  have : Countable (RootOccurrence f q top β j) := by
    unfold RootOccurrence
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have ht := maximal_bad_countable_tail (ι := RootOccurrence f q top β j) q top f
    (fun a => a.1.1) (fun a => a.1.2.1) (fun a => a.1.2.2)
    (fun a b hb hl hp => Subtype.ext (Prod.ext hb (Prod.ext hl hp))) hβ hC
    (fun a => a.property.1) hf hbound hsum top j (fun a => a.property.2) hlambda
  convert ht using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  by_cases hx : x ∈ cell q top j
  · simp only [mem_inter_iff, mem_ofPred_eq, hx, and_true,
      gridCount_eq_rootCount f q top β j hx]
  · simp only [mem_inter_iff, hx, and_false]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable line-counting lemma used for simultaneous separated directions. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

open DyadicLineGrid

/-- A single jointly measurable count dominates every finite collection of
popular bins, and its tail is exponentially small on every bounded interval.
Only finite partial sums of the countable bin family are needed as data. -/
theorem line_counting {X B : Type*} [MeasurableSpace X] [Countable B]
    (f : B → X × ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    (hbound : ∀ b p, 0 ≤ f b p ∧ f b p ≤ 1)
    {C H θ : ℝ} (hC : 0 < C) (hH : 0 < H) (hθ : 0 < θ)
    (hsum : ∀ s : Finset B, ∀ p, (∑ b ∈ s, f b p) ≤ C) :
    ∃ N : X × ℝ → ℝ≥0∞, Measurable N ∧
      (∀ (p : X × ℝ) (bins : Finset B), (∀ b ∈ bins, ∃ a c : ℝ, a < c ∧ c - a ≤ H ∧ p.2 ∈ Icc a c ∧
        θ * (c - a) ≤ ∫ x in Icc a c, f b (p.1, x)) → (bins.card : ℝ≥0∞) ≤ N p) ∧
      ∀ (p : X) (a b : ℝ), a ≤ b → ∀ lambda : ℝ, 0 ≤ lambda →
        volume.real ({x | ENNReal.ofReal lambda < N (p, x)} ∩ Icc a b) ≤
          96 * (b - a + H) * Real.exp (-θ * lambda / (24 * C)) := by
  obtain ⟨top, htop0, htop1⟩ := exists_root_scale hH
  refine ⟨selectedCount f top (θ / 6), measurable_selectedCount f hf top (θ / 6), ?_, ?_⟩
  · intro p bins hb
    exact popular_bins_card_le_selectedCount f hf hbound hθ.le htop0 p bins hb
  · intro p a b hab lambda hlambda
    have hβ : 0 < θ / 6 := by positivity
    let fl : B → ℝ → ℝ := fun bin x => f bin (p, x)
    have hfl : ∀ bin, Measurable (fl bin) := fun bin =>
      (hf bin).comp (measurable_const.prodMk measurable_id)
    have hg := two_dyadic_root_exponential_tail_scale (A := C / (θ / 6)) (H := H) top hab
      (div_pos hC hβ) hlambda htop1.le
      (fun q => gridCount fl q top (θ / 6)) (by
        intro q _ j _ t ht
        have h := gridCount_root_tail fl q top hβ hC hfl
          (fun bin x => hbound bin (p, x)) (fun s x => hsum s (p, x)) j ht
        simpa only [cell_length] using h)
    have hexp : -lambda / (4 * (C / (θ / 6))) = -θ * lambda / (24 * C) := by
      field_simp [hC.ne', hθ.ne']
      ring
    rw [hexp] at hg
    convert hg using 2
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, selectedCount_eq_gridCounts, fl]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCountSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the line-counting tail across a finite transverse interval. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

theorem measurableSet_lineCountSlab (N : ℝ × ℝ → ℝ≥0∞) (hN : Measurable N)
    (U V : Set ℝ) (hU : MeasurableSet U) (hV : MeasurableSet V) (lambda : ℝ) :
    MeasurableSet (lineCountSlab N U V lambda) :=
  (hU.prod hV).inter (measurableSet_lt measurable_const (hN.comp measurable_swap))

theorem lineCountSlab_measure_bound (N : ℝ × ℝ → ℝ≥0∞) (hN : Measurable N)
    (U V : Set ℝ) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUf : volume U ≠ ∞) (hVf : volume V ≠ ∞) {lambda M : ℝ} (hM : 0 ≤ M)
    (htail : ∀ y ∈ V, volume.real ({x | ENNReal.ofReal lambda < N (y, x)} ∩ U) ≤ M) :
    (volume.prod volume).real (lineCountSlab N U V lambda) ≤ M * volume.real V := by
  apply section_measure_bound _ (measurableSet_lineCountSlab N hN U V hU hV lambda)
    U V hV hUf hVf inter_subset_left hM
  intro y hy
  have heq : (fun x => (x, y)) ⁻¹' lineCountSlab N U V lambda =
      {x | ENNReal.ofReal lambda < N (y, x)} ∩ U := by
    ext x
    simp only [lineCountSlab, mem_preimage, mem_inter_iff, mem_prod, hy, and_true, mem_ofPred_eq]
    exact and_comm
  rw [heq]
  exact htail y hy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable planar exceptional set attached to one reference top. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

theorem measurableSet_referenceException (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞)
    (hN : Measurable N) (K lambda : ℝ) : MeasurableSet (T.referenceException N K lambda) := by
  apply T.referenceChart.measurableSet_image.mpr
  exact LipschitzHilbert.measurableSet_lineCountSlab N hN _ _ measurableSet_Icc measurableSet_Icc lambda

theorem referenceException_measure_bound (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞)
    (hN : Measurable N) {K lambda M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (htail : ∀ v ∈ Icc (-K * T.width) (K * T.width),
      volume.real ({x | ENNReal.ofReal lambda < N (v, x)} ∩ T.witnessInterval K) ≤ M) :
    (volume.prod volume).real (T.referenceException N K lambda) ≤ M * (2 * K * T.width) := by
  have harea : (volume.prod volume).real (T.referenceException N K lambda) =
      (volume.prod volume).real (LipschitzHilbert.lineCountSlab N (T.witnessInterval K)
        (Icc (-K * T.width) (K * T.width)) lambda) :=
    congrArg ENNReal.toReal (T.referenceChart_image_measure _)
  rw [harea]
  have h := LipschitzHilbert.lineCountSlab_measure_bound N hN _ _ measurableSet_Icc measurableSet_Icc
    measure_Icc_lt_top.ne measure_Icc_lt_top.ne hM htail
  have hlen : volume.real (Icc (-K * T.width) (K * T.width)) = 2 * K * T.width := by
    rw [Real.volume_real_Icc_of_le (by nlinarith [T.width_pos])]
    ring
  simpa only [hlen, witnessInterval] using h

/-- At every significant point outside this fixed exceptional set, the
reference-line count is below the chosen threshold. -/
theorem count_le_outside_referenceException (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞)
    {K lambda : ℝ} {z : ℝ × ℝ} (hz : T.radius z ≤ K)
    (hout : z ∉ T.referenceException N K lambda) :
    N ((T.referenceChart.symm z).2, z.1) ≤ ENNReal.ofReal lambda := by
  apply le_of_not_gt
  intro hlt
  apply hout
  refine ⟨T.referenceChart.symm z, ?_, T.referenceChart.apply_symm_apply z⟩
  refine ⟨T.significant_mem_referenceRectangle hz, ?_⟩
  exact hlt

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SeparatedPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinality of separated frequencies in one bounded interval. -/

noncomputable section

namespace LipschitzHilbert.PhaseCombinatorics

theorem ordered_separated_index_bound {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ)
    (hf : StrictMono f) {gap : ℝ} (hsep : Separated f gap) (i : Fin N) :
    (i.val : ℝ) * gap ≤ f i - f ⟨0, hN⟩ := by
  have h (k : ℕ) (hk : k < N) : (k : ℝ) * gap ≤ f ⟨k, hk⟩ - f ⟨0, hN⟩ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < N := by omega
      have hstep := @hsep (⟨k + 1, hk⟩ : Fin N) ⟨k, hk'⟩ (by
        intro heq
        have hv := congrArg Fin.val heq
        change k + 1 = k at hv
        omega)
      have hmono : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := hf (by
        change k < k + 1
        omega)
      rw [abs_of_pos (sub_pos.mpr hmono)] at hstep
      have hprev := ih hk'
      push_cast
      nlinarith
  exact h i.val i.isLt

theorem separated_card_le_span {ι : Type*} [Fintype ι] (frequency : ι → ℝ)
    {gap a b : ℝ} (hgap : 0 < gap) (hab : a ≤ b)
    (hsep : Separated frequency gap) (hbound : ∀ i, a ≤ frequency i ∧ frequency i ≤ b) :
    (Fintype.card ι : ℝ) ≤ 1 + (b - a) / gap := by
  classical
  by_cases hN : Fintype.card ι = 0
  · rw [hN]
    have hdiv := div_nonneg (sub_nonneg.mpr hab) hgap.le
    norm_num
    linarith
  · have hNpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hN
    have hinj : Function.Injective frequency := by
      intro i j hij
      by_contra hne
      have h := @hsep i j hne
      rw [hij, sub_self, abs_zero] at h
      linarith
    let : LinearOrder ι := LinearOrder.lift' frequency hinj
    let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
    have hf : StrictMono (fun i => frequency (e i)) := fun _ _ hij => e.strictMono hij
    have he_sep : Separated (fun i => frequency (e i)) gap := by
      intro i j hij
      exact @hsep (e i) (e j) (fun h => hij (e.injective h))
    let last : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
    have hindex := ordered_separated_index_bound hNpos _ hf he_sep last
    have hspan : ((Fintype.card ι : ℝ) - 1) * gap ≤ b - a := by
      have hlast := (hbound (e last)).2
      have hfirst := (hbound (e ⟨0, hNpos⟩)).1
      dsimp only [last] at hindex
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one] at hindex
      linarith
    have hdiv := (le_div_iff₀ hgap).2 hspan
    linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual angular annulus bins

The positive and negative dyadic annuli about a reference slope are each
partitioned into `M` equal half-open bins, as in §6 of the manuscript.
Enlargement is concentric. No choice of a significant list enters these
definitions.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.AngularBins

theorem radialCoordinate_abs (s a : ℝ) (positive : Bool) :
    |radialCoordinate s positive a| = |a - s| := by
  cases positive <;> simp [radialCoordinate, abs_sub_comm]

theorem radialCoordinate_sub_abs (s a a' : ℝ) (positive : Bool) :
    |radialCoordinate s positive a - radialCoordinate s positive a'| = |a - a'| := by
  cases positive <;> simp only [radialCoordinate, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · have h : (s - a) - (s - a') = -(a - a') := by ring
    rw [h, abs_neg]
  · congr 1
    ring

theorem width_pos {M : ℕ} (hM : 0 < M) (h : ℤ) : 0 < width M h :=
  div_pos (DyadicLineGrid.scale_pos h) (by exact_mod_cast hM)

theorem width_mul {M : ℕ} (hM : 0 < M) (h : ℤ) :
    (M : ℝ) * width M h = DyadicLineGrid.scale h := by
  unfold width
  field_simp [show (M : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hM]

theorem continuous_radialCoordinate (s : ℝ) (positive : Bool) :
    Continuous (radialCoordinate s positive) := by
  cases positive
  · change Continuous (fun a : ℝ => s - a)
    exact continuous_const.sub continuous_id
  · change Continuous (fun a : ℝ => a - s)
    exact continuous_id.sub continuous_const

theorem measurableSet_enlargedBin (s c : ℝ) {M : ℕ} (b : Bin M) :
    MeasurableSet (enlargedBin s c b) :=
  measurableSet_le (((continuous_radialCoordinate s b.1).sub continuous_const).abs.measurable)
    measurable_const

/-- Every slope other than the reference belongs to an actual angular bin. -/
theorem exists_baseBin (s : ℝ) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : a ≠ s) :
    ∃ b : Bin M, a ∈ baseBin s b := by
  have hr : 0 < |a - s| := abs_pos.mpr (sub_ne_zero.mpr ha)
  obtain ⟨h, hh0, hh1⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 2)
  change DyadicLineGrid.scale h ≤ |a - s| at hh0
  change |a - s| < DyadicLineGrid.scale (h + 1) at hh1
  rw [DyadicLineGrid.scale_succ] at hh1
  have hw := width_pos hM h
  have hm := width_mul hM h
  let x : ℝ := (|a - s| - DyadicLineGrid.scale h) / width M h
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr hh0) hw.le
  have hxM : x < M := (div_lt_iff₀ hw).mpr (by nlinarith)
  let j : Fin M := ⟨⌊x⌋₊, (Nat.floor_lt hx0).mpr hxM⟩
  have hj0 := mul_le_mul_of_nonneg_right (Nat.floor_le hx0) hw.le
  have hj1 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) hw
  have hxw : x * width M h = |a - s| - DyadicLineGrid.scale h := by
    dsimp only [x]
    exact div_mul_cancel₀ _ hw.ne'
  rw [hxw] at hj0 hj1
  have hrad : ∃ positive : Bool, radialCoordinate s positive a = |a - s| := by
    by_cases hsa : s ≤ a
    · exact ⟨true, by simp [radialCoordinate, abs_of_nonneg (sub_nonneg.mpr hsa)]⟩
    · exact ⟨false, by simp [radialCoordinate, abs_of_neg (sub_neg.mpr (lt_of_not_ge hsa))]⟩
  obtain ⟨positive, hpositive⟩ := hrad
  refine ⟨(positive, h, j), ?_⟩
  change radialStart M h j ≤ radialCoordinate s positive a ∧
    radialCoordinate s positive a < radialStart M h j + width M h
  rw [hpositive]
  dsimp only [radialStart, j]
  constructor <;> nlinarith

theorem baseBin_radial_bounds (s : ℝ) {M : ℕ} (hM : 0 < M)
    {b : Bin M} {a : ℝ} (ha : a ∈ baseBin s b) :
    DyadicLineGrid.scale b.2.1 ≤ |a - s| ∧
      |a - s| < 2 * DyadicLineGrid.scale b.2.1 := by
  have hw := width_pos hM b.2.1
  have hm := width_mul hM b.2.1
  have hj0 : (0 : ℝ) ≤ b.2.2 := Nat.cast_nonneg _
  have hj1 : (b.2.2 : ℝ) + 1 ≤ M := by exact_mod_cast b.2.2.isLt
  have hstart : DyadicLineGrid.scale b.2.1 ≤ radialStart M b.2.1 b.2.2 := by
    unfold radialStart
    linarith [mul_nonneg hj0 hw.le]
  have hend : radialStart M b.2.1 b.2.2 + width M b.2.1 ≤
      2 * DyadicLineGrid.scale b.2.1 := by
    have hmul := mul_le_mul_of_nonneg_right hj1 hw.le
    unfold radialStart
    nlinarith
  have ha' : 0 ≤ radialCoordinate s b.1 a :=
    (DyadicLineGrid.scale_pos b.2.1).le.trans (hstart.trans ha.1)
  rw [← radialCoordinate_abs s a b.1, abs_of_nonneg ha']
  exact ⟨hstart.trans ha.1, ha.2.trans_le hend⟩

theorem baseBin_diameter_lt (s : ℝ) {M : ℕ} (b : Bin M)
    {a a' : ℝ} (ha : a ∈ baseBin s b) (ha' : a' ∈ baseBin s b) :
    |a - a'| < width M b.2.1 := by
  rw [← radialCoordinate_sub_abs s a a' b.1]
  exact abs_lt.mpr ⟨by linarith [ha.1, ha'.2], by linarith [ha.2, ha'.1]⟩

/-- A perturbation of a base-bin slope by at most `(c-1)/2` bin widths
lies in its concentric enlargement. -/
theorem nearby_mem_enlargedBin (s : ℝ) {M : ℕ} (b : Bin M) {c a a' : ℝ}
    (ha : a ∈ baseBin s b)
    (hnear : |a' - a| ≤ (c - 1) * width M b.2.1 / 2) :
    a' ∈ enlargedBin s c b := by
  have hbase : |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
      width M b.2.1 / 2 := by
    unfold radialMidpoint
    exact abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have htri := abs_add_le (radialCoordinate s b.1 a' - radialCoordinate s b.1 a)
    (radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2)
  rw [sub_add_sub_cancel, radialCoordinate_sub_abs] at htri
  change |radialCoordinate s b.1 a' - radialMidpoint M b.2.1 b.2.2| ≤ _
  linarith

/-- A separated list occupies distinct bins whenever those bins are
strictly narrower than the separation scale. -/
theorem assigned_bins_injective {ι : Type*} (s : ℝ) {M : ℕ}
    (frequency : ι → ℝ) (bin : ι → Bin M) {rho : ℝ}
    (hsep : PhaseCombinatorics.Separated frequency rho)
    (hmem : ∀ i, frequency i ∈ baseBin s (bin i))
    (hwidth : ∀ i, width M (bin i).2.1 < rho) : Function.Injective bin := by
  intro i j hij
  by_contra hne
  have hdiam := baseBin_diameter_lt s (bin i) (hmem i) (by simpa only [hij] using hmem j)
  exact (not_lt_of_ge (hsep hne)) (hdiam.trans (hwidth i))

end LipschitzHilbert.AngularBins

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBinOverlap
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed overlap of the enlarged angular annulus bins from §6. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.AngularBins

attribute [local instance] Classical.propDecidable

theorem enlargedBin_radial_bounds (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hcM : c ≤ M) {b : Bin M} {a : ℝ}
    (ha : a ∈ enlargedBin s c b) :
    DyadicLineGrid.scale b.2.1 / 2 ≤ |a - s| ∧
      |a - s| ≤ 5 * DyadicLineGrid.scale b.2.1 / 2 := by
  have hw := width_pos hM b.2.1
  have hm := width_mul hM b.2.1
  have hj0 : (0 : ℝ) ≤ b.2.2 := Nat.cast_nonneg _
  have hj1 : (b.2.2 : ℝ) + 1 ≤ M := by exact_mod_cast b.2.2.isLt
  have hmid0 : DyadicLineGrid.scale b.2.1 ≤ radialMidpoint M b.2.1 b.2.2 := by
    unfold radialMidpoint radialStart
    nlinarith [mul_nonneg hj0 hw.le]
  have hmid1 : radialMidpoint M b.2.1 b.2.2 ≤ 2 * DyadicLineGrid.scale b.2.1 := by
    have hmul := mul_le_mul_of_nonneg_right hj1 hw.le
    unfold radialMidpoint radialStart
    nlinarith
  have hrad := mul_le_mul_of_nonneg_right hcM hw.le
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤ _ at ha
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  have hcoord : 0 ≤ radialCoordinate s b.1 a := by
    have hs := DyadicLineGrid.scale_pos b.2.1
    nlinarith
  rw [← radialCoordinate_abs s a b.1, abs_of_nonneg hcoord]
  constructor <;> nlinarith

/-- Any two enlarged annuli covering the same point have levels differing
by at most two, uniformly in the number of angular subdivisions. -/
theorem enlargedBin_levels_near (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hcM : c ≤ M) {b b' : Bin M} {a : ℝ}
    (ha : a ∈ enlargedBin s c b) (ha' : a ∈ enlargedBin s c b') :
    b'.2.1 - 2 ≤ b.2.1 ∧ b.2.1 ≤ b'.2.1 + 2 := by
  have hb := enlargedBin_radial_bounds s hM hcM ha
  have hb' := enlargedBin_radial_bounds s hM hcM ha'
  have hlevel {i j : ℤ} (hij : DyadicLineGrid.scale i ≤ 5 * DyadicLineGrid.scale j) :
      i ≤ j + 2 := by
    by_contra hn
    have hji : j + 3 ≤ i := by omega
    have hpow : DyadicLineGrid.scale (j + 3) ≤ DyadicLineGrid.scale i :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hji
    have heq : DyadicLineGrid.scale (j + 3) = 8 * DyadicLineGrid.scale j := by
      simp only [DyadicLineGrid.scale, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    rw [heq] at hpow
    have hs := DyadicLineGrid.scale_pos j
    linarith
  constructor
  · have h := hlevel (show DyadicLineGrid.scale b'.2.1 ≤
        5 * DyadicLineGrid.scale b.2.1 by linarith)
    omega
  · exact hlevel (by linarith)

theorem radialMidpoint_separated {M : ℕ} (hM : 0 < M) (h : ℤ) :
    PhaseCombinatorics.Separated (radialMidpoint M h) (width M h) := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hcast : 1 ≤ |(i : ℝ) - (j : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have heq : radialMidpoint M h i - radialMidpoint M h j =
      ((i : ℝ) - j) * width M h := by
    unfold radialMidpoint radialStart
    ring
  rw [heq, abs_mul, abs_of_pos (width_pos hM h)]
  exact le_mul_of_one_le_left (width_pos hM h).le hcast

theorem finite_level_overlap (s a : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (positive : Bool) (h : ℤ) (t : Finset (Fin M))
    (ht : ∀ j ∈ t, a ∈ enlargedBin s c (positive, h, j)) :
    (t.card : ℝ) ≤ 1 + c := by
  have hw := width_pos hM h
  have hsep : PhaseCombinatorics.Separated (fun j : t => radialMidpoint M h j.1)
      (width M h) := by
    intro i j hij
    exact radialMidpoint_separated hM h (fun heq => hij (Subtype.ext heq))
  have hbounds : ∀ j : t,
      radialCoordinate s positive a - c * width M h / 2 ≤ radialMidpoint M h j.1 ∧
      radialMidpoint M h j.1 ≤ radialCoordinate s positive a + c * width M h / 2 := by
    intro j
    have hj := ht j.1 j.2
    change |radialCoordinate s positive a - radialMidpoint M h j.1| ≤
      c * width M h / 2 at hj
    obtain ⟨hj0, hj1⟩ := abs_le.mp hj
    constructor <;> linarith
  have hpack := PhaseCombinatorics.separated_card_le_span _ hw
    (show radialCoordinate s positive a - c * width M h / 2 ≤
      radialCoordinate s positive a + c * width M h / 2 by
        nlinarith [mul_nonneg hc hw.le])
    hsep hbounds
  have heq : ((radialCoordinate s positive a + c * width M h / 2) -
      (radialCoordinate s positive a - c * width M h / 2)) / width M h = c := by
    field_simp [hw.ne']
    ring
  simpa only [Fintype.card_coe, heq] using hpack

/-- The enlarged annulus bins have uniformly bounded multiplicity. The
constant includes both signs, so no boundary case requires choosing the
sign of the evaluation point. -/
theorem finite_overlap_card (s a : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) (t : Finset (Bin M))
    (ht : ∀ b ∈ t, a ∈ enlargedBin s c b) :
    (t.card : ℝ) ≤ 10 * (1 + c) := by
  classical
  by_cases hempty : t = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨b₀, hb₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let p : Bin M → Bool × ℤ := fun b => (b.1, b.2.1)
  let levels : Finset (Bool × ℤ) := Finset.univ.product
    (Finset.Icc (b₀.2.1 - 2) (b₀.2.1 + 2))
  have hmaps : (t : Set (Bin M)).MapsTo p levels := by
    intro b hb
    have hnear := enlargedBin_levels_near s hM hcM (ht b hb) (ht b₀ hb₀)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr hnear⟩
  have hlevels : levels.card = 10 := by
    have hcard : ((Finset.Icc (b₀.2.1 - 2) (b₀.2.1 + 2)).card : ℤ) = 5 := by
      rw [Int.card_Icc_of_le (a := b₀.2.1 - 2) (b := b₀.2.1 + 2) (by omega)]
      omega
    have hcard' : (Finset.Icc (b₀.2.1 - 2) (b₀.2.1 + 2)).card = 5 := by
      exact_mod_cast hcard
    simp [levels, Finset.card_product, hcard']
  have hfiber (v : Bool × ℤ) :
      ((t.filter (fun b => p b = v)).card : ℝ) ≤ 1 + c := by
    let u := t.filter (fun b => p b = v)
    let slots := u.image (fun b => b.2.2)
    have hinj : (u : Set (Bin M)).InjOn (fun b => b.2.2) := by
      intro b hb b' hb' heq
      have hp := (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hb').2.symm
      exact Prod.ext (congrArg (fun v : Bool × ℤ => v.1) hp)
        (Prod.ext (congrArg (fun v : Bool × ℤ => v.2) hp) heq)
    have hslots : slots.card = u.card := Finset.card_image_of_injOn hinj
    have h := finite_level_overlap s a hM hc v.1 v.2 slots (by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      have hpair := (Finset.mem_filter.mp hb).2
      have heq : (v.1, v.2, b.2.2) = b := by
        exact Prod.ext (congrArg (fun v : Bool × ℤ => v.1) hpair.symm)
          (Prod.ext (congrArg (fun v : Bool × ℤ => v.2) hpair.symm) rfl)
      rw [heq]
      exact ht b (Finset.mem_filter.mp hb).1)
    simpa only [hslots] using h
  calc
    (t.card : ℝ) = ∑ v ∈ levels, ((t.filter (fun b => p b = v)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    _ ≤ ∑ _v ∈ levels, (1 + c) := Finset.sum_le_sum fun v _ => hfiber v
    _ = 10 * (1 + c) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hlevels, Nat.cast_ofNat]

/-- Every finite family of the actual bin indicator functions has the
same uniform pointwise bound required by the line-counting lemma. -/
theorem finite_indicator_overlap (s a : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) (t : Finset (Bin M)) :
    (∑ b ∈ t, (enlargedBin s c b).indicator (1 : ℝ → ℝ) a) ≤ 10 * (1 + c) := by
  classical
  have h := finite_overlap_card s a hM hc hcM
    (t.filter (fun b => a ∈ enlargedBin s c b)) (by
      intro b hb
      exact (Finset.mem_filter.mp hb).2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum,
    Set.indicator_apply, Pi.one_apply]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> norm_num

theorem measurable_binFunction {X : Type*} [MeasurableSpace X]
    (s c : ℝ) {M : ℕ} (u : X → ℝ) (hu : Measurable u) (b : Bin M) :
    Measurable (binFunction s c u b) :=
  (measurable_one.indicator (measurableSet_enlargedBin s c b)).comp hu

theorem binFunction_bounds {X : Type*} (s c : ℝ) {M : ℕ} (u : X → ℝ)
    (b : Bin M) (x : X) : 0 ≤ binFunction s c u b x ∧ binFunction s c u b x ≤ 1 := by
  by_cases hx : u x ∈ enlargedBin s c b <;> simp [binFunction, Set.indicator, hx]

theorem finite_binFunction_sum {X : Type*} (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) (u : X → ℝ)
    (t : Finset (Bin M)) (x : X) :
    (∑ b ∈ t, binFunction s c u b x) ≤ 10 * (1 + c) :=
  finite_indicator_overlap s (u x) hM hc hcM t

end LipschitzHilbert.AngularBins

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularLineCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line-counting theorem instantiated with the actual angular bins. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.AngularBins

/-- A single jointly measurable count for every reference line and every
angular bin. Its definition is independent of the separated list later
tested against it. The overlap constant is the proved `10*(1+c)`. -/
theorem angular_line_counting {X : Type*} [MeasurableSpace X]
    (s : ℝ) {M : ℕ} (hM : 0 < M) {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M)
    (u : X × ℝ → ℝ) (hu : Measurable u)
    {H θ : ℝ} (hH : 0 < H) (hθ : 0 < θ) :
    ∃ N : X × ℝ → ℝ≥0∞, Measurable N ∧
      (∀ (p : X × ℝ) (bins : Finset (Bin M)),
        (∀ b ∈ bins, ∃ a d : ℝ, a < d ∧ d - a ≤ H ∧ p.2 ∈ Icc a d ∧
          θ * (d - a) ≤ ∫ x in Icc a d, binFunction s c u b (p.1, x)) →
        (bins.card : ℝ≥0∞) ≤ N p) ∧
      ∀ (p : X) (a b : ℝ), a ≤ b → ∀ lambda : ℝ, 0 ≤ lambda →
        volume.real ({x | ENNReal.ofReal lambda < N (p, x)} ∩ Icc a b) ≤
          96 * (b - a + H) * Real.exp (-θ * lambda / (240 * (1 + c))) := by
  obtain ⟨N, hN, hpopular, htail⟩ := line_counting
    (fun b => binFunction s c u b)
    (fun b => measurable_binFunction s c u hu b)
    (fun b p => binFunction_bounds s c u b p)
    (show 0 < 10 * (1 + c) by positivity) hH hθ
    (fun t p => finite_binFunction_sum s hM hc hcM u t p)
  refine ⟨N, hN, hpopular, ?_⟩
  intro p a b hab lambda hlambda
  simpa only [show (24 : ℝ) * (10 * (1 + c)) = 240 * (1 + c) by ring] using
    htail p a b hab lambda hlambda

end LipschitzHilbert.AngularBins

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ReferenceLineCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One list-independent angular count and exceptional set per reference top. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

theorem measurable_referenceSlope (R : SlopeBox) (u : ℝ × ℝ → ℝ) (hu : Measurable u) :
    Measurable (R.referenceSlope u) :=
  hu.comp (R.referenceChart.measurable.comp measurable_swap)

theorem referenceBinFunction_eq (R : SlopeBox) (u : ℝ × ℝ → ℝ) (c : ℝ)
    {M : ℕ} (b : AngularBins.Bin M) (z : ℝ × ℝ) (x : ℝ) :
    AngularBins.binFunction R.slope c (R.referenceSlope u) b
        ((R.referenceChart.symm z).2, x) =
      (LipschitzHilbert.lineBinSet u R.slope z (AngularBins.enlargedBin R.slope c b)).indicator
        (fun _ => (1 : ℝ)) x := by
  unfold AngularBins.binFunction referenceSlope
  rw [R.referenceChart_linePoint]
  classical
  by_cases h : u (linePoint R.slope z x) ∈ AngularBins.enlargedBin R.slope c b
  · have h' : x ∈ lineBinSet u R.slope z (AngularBins.enlargedBin R.slope c b) := h
    rw [indicator_of_mem h, indicator_of_mem h']
    rfl
  · have h' : x ∉ lineBinSet u R.slope z (AngularBins.enlargedBin R.slope c b) := h
    rw [indicator_of_notMem h, indicator_of_notMem h']

/-- The actual angular bins on a reference line admit a common count and
exponentially small planar exceptional set, independently of any list. -/
theorem reference_count_setup (R : SlopeBox) (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    {M : ℕ} (hM : 0 < M) {c K P θ : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M)
    (hK : 0 ≤ K) (hP : 0 < P) (hθ : 0 < θ) :
    ∃ N : ℝ × ℝ → ℝ≥0∞, Measurable N ∧
      R.ReferencePopularCount u c P θ M N ∧
      ∀ lambda : ℝ, 0 ≤ lambda →
        (volume.prod volume).real (R.referenceException N K lambda) ≤
          384 * K * (K + P) * R.length * R.width *
            Real.exp (-θ * lambda / (240 * (1 + c))) := by
  have hl := R.length_pos
  have hw := R.width_pos
  obtain ⟨N, hN, hpopular, htail⟩ := AngularBins.angular_line_counting R.slope hM hc hcM
    (R.referenceSlope u) (R.measurable_referenceSlope u hu)
    (show 0 < 2 * P * R.length by positivity) hθ
  refine ⟨N, hN, hpopular, ?_⟩
  intro lambda hlambda
  let e := Real.exp (-θ * lambda / (240 * (1 + c)))
  have he : 0 < e := Real.exp_pos _
  have hbound : (volume.prod volume).real (R.referenceException N K lambda) ≤
      (96 * (2 * K * R.length + 2 * P * R.length) * e) * (2 * K * R.width) := by
    apply R.referenceException_measure_bound N hN hK (by positivity)
    intro v _
    have h := htail v (R.x - K * R.length) (R.x + K * R.length)
      (by nlinarith) lambda hlambda
    have heq : R.x + K * R.length - (R.x - K * R.length) = 2 * K * R.length := by ring
    simpa only [witnessInterval, heq] using h
  calc
    _ ≤ _ := hbound
    _ = _ := by dsimp only [e]; ring

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WitnessBinCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact popularity witnesses give a simultaneous reference-line count. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

/-- Every compact witness supplies one of the popular bins counted by the
same reference count. The count was chosen independently of this finite list. -/
theorem compact_witness_list_count {ι : Type*} [DecidableEq ι]
    (R : SlopeBox) (T : ι → SlopeBox) (I : Finset ι)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (z : ℝ × ℝ)
    {A q P θ c : ℝ} {M : ℕ} (hA : 0 < A) (hq : 0 ≤ q)
    (hP : 0 < P) (hAP : A ≤ P) (hθ : θ ≤ q / (4 * A * P))
    (E : ι → Set (ℝ × ℝ)) (bin : ι → AngularBins.Bin M)
    (hbin : Set.InjOn bin I)
    (hcompact : ∀ i ∈ I, IsCompact (E i))
    (hbox : ∀ i ∈ I, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i ∈ I, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hlength : ∀ i ∈ I, (T i).length ≤ R.length)
    (hz : ∀ i ∈ I, (T i).radius z ≤ P)
    (htransfer : ∀ i ∈ I, ∀ w ∈ E i,
      u (referencePoint R.slope z w) ∈ AngularBins.enlargedBin R.slope c (bin i))
    (N : ℝ × ℝ → ℝ≥0∞) (hN : R.ReferencePopularCount u c P θ M N) :
    (I.card : ℝ≥0∞) ≤ N ((R.referenceChart.symm z).2, z.1) := by
  classical
  have hpopular : ∀ b ∈ I.image bin, ∃ a d : ℝ,
      a < d ∧ d - a ≤ 2 * P * R.length ∧ z.1 ∈ Icc a d ∧
        θ * (d - a) ≤ ∫ x in Icc a d,
          AngularBins.binFunction R.slope c (R.referenceSlope u) b
            ((R.referenceChart.symm z).2, x) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    have hl := (T i).length_pos
    obtain ⟨hmem, havg⟩ := (T i).witness_centered_line_average (E i) (hcompact i hi)
      hA hq hP hAP (hbox i hi) (harea i hi) u hu R.slope z (hz i hi)
      (AngularBins.enlargedBin R.slope c (bin i))
      (AngularBins.measurableSet_enlargedBin _ _ _) (htransfer i hi)
    refine ⟨(T i).x - P * (T i).length, (T i).x + P * (T i).length,
      by nlinarith, ?_, hmem, ?_⟩
    · have h := mul_le_mul_of_nonneg_left (hlength i hi) (show 0 ≤ 2 * P by positivity)
      nlinarith
    · have hlen := (T i).witnessInterval_length hP.le
      have hlenpos : 0 < volume.real ((T i).witnessInterval P) := by
        rw [hlen]
        positivity
      have hint := (le_div_iff₀ hlenpos).mp (hθ.trans havg)
      rw [hlen] at hint
      have heq : (T i).x + P * (T i).length - ((T i).x - P * (T i).length) =
          2 * P * (T i).length := by ring
      rw [heq]
      simp_rw [R.referenceBinFunction_eq]
      exact hint
  have h := hN ((R.referenceChart.symm z).2, z.1) (I.image bin) hpopular
  rwa [Finset.card_image_of_injOn hbin] at h

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBinTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Angular-bin transfer for a separated list

These are the quantitative bin-width and enlargement calculations used
after transferring a popularity witness to a reference line in §6.
-/

noncomputable section

namespace LipschitzHilbert.AngularBins

theorem baseBin_width_le_relative (s : ℝ) {M : ℕ} (hM : 0 < M)
    {B rho a : ℝ} (hB : 0 < B) (hMB : (M : ℝ) = B ^ 2)
    {b : Bin M} (ha : a ∈ baseBin s b) (hrelative : |a - s| ≤ B * rho) :
    width M b.2.1 ≤ rho / B := by
  have hs := (baseBin_radial_bounds s hM ha).1
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    width M b.2.1 ≤ (B * rho) / M :=
      div_le_div_of_nonneg_right (hs.trans hrelative) hm.le
    _ = rho / B := by rw [hMB]; field_simp [ne_of_gt hB]

theorem baseBin_width_lt_separation (s : ℝ) {M : ℕ} (hM : 0 < M)
    {B rho a : ℝ} (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2)
    {b : Bin M} (ha : a ∈ baseBin s b) (hrelative : |a - s| ≤ B * rho) :
    width M b.2.1 < rho := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  refine (baseBin_width_le_relative s hM hB0 hMB ha hrelative).trans_lt ?_
  exact (div_lt_iff₀ hB0).mpr (by nlinarith)

/-- The bins chosen for a separated list are distinct, since their
widths are at most `rho/B` with `B>1`. -/
theorem separated_annulus_bins_injective {ι : Type*} (s : ℝ) {M : ℕ} (hM : 0 < M)
    {B rho : ℝ} (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2)
    (frequency : ι → ℝ) (bin : ι → Bin M)
    (hsep : PhaseCombinatorics.Separated frequency rho)
    (hmem : ∀ i, frequency i ∈ baseBin s (bin i))
    (hrelative : ∀ i, |frequency i - s| ≤ B * rho) : Function.Injective bin :=
  assigned_bins_injective s frequency bin hsep hmem (fun i =>
    baseBin_width_lt_separation s hM hB hrho hMB (hmem i) (hrelative i))

theorem enlargedBin_mono (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c c' : ℝ} (hcc' : c ≤ c') (b : Bin M) :
    enlargedBin s c b ⊆ enlargedBin s c' b := by
  intro a ha
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
    c * width M b.2.1 / 2 at ha
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
    c' * width M b.2.1 / 2
  exact ha.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc' (width_pos hM b.2.1).le) (by norm_num))

/-- The transferred witness error is at most `(c0+1) Delta/M`.
The annulus relation `Delta<2*2^h` makes a fixed concentric enlargement
sufficient for every scale and every separated list. -/
theorem transferred_slope_mem_enlarged (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c0 c a a' : ℝ} (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    {b : Bin M} (ha : a ∈ baseBin s b)
    (herror : |a' - a| ≤ (c0 + 1) * |a - s| / M) :
    a' ∈ enlargedBin s c b := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hrad := (baseBin_radial_bounds s hM ha).2.le
  have herror' : |a' - a| ≤ 2 * (c0 + 1) * width M b.2.1 := by
    calc
      |a' - a| ≤ (c0 + 1) * |a - s| / M := herror
      _ ≤ (c0 + 1) * (2 * DyadicLineGrid.scale b.2.1) / M :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (by linarith)) hm.le
      _ = 2 * (c0 + 1) * width M b.2.1 := by unfold width; ring
  apply enlargedBin_mono s hM hc b
  apply nearby_mem_enlargedBin s b ha
  convert herror' using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert.AngularBins

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SeparatedWitnessCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference count controls every separated list of popular tops. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LipschitzHilbert.SlopeBox

/-- Extract compact witnesses, transfer them to the reference line, and
assign distinct angular bins. The reference count is fixed before the list. -/
theorem separated_witness_list_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SlopeBox) (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ)
    {L : ℝ≥0} (hu : LipschitzWith L u) (z : ℝ × ℝ)
    {M : ℕ} (hM : 0 < M) {A q P K θ c c0 B rho m : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hP : 0 < P) (hK : 0 ≤ K)
    (hAK : A + K ≤ P) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (hθ : θ ≤ q / (8 * A * P))
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i, 0 ≤ d i) (hwidth : ∀ i, (T i).width = m * (T i).length * d i)
    (hprecision : ∀ i, d i ≤ rho / B ^ 2)
    (hsmall : ∀ i, L * P * m * (T i).length ≤ 1 / 2)
    (hlower : ∀ i, rho ≤ |(T i).slope - R.slope|)
    (hupper : ∀ i, |(T i).slope - R.slope| ≤ B * rho)
    (hsep : PhaseCombinatorics.Separated (fun i => (T i).slope) rho)
    (hlength : ∀ i, (T i).length ≤ R.length)
    (hz : ∀ i, (T i).radius z ≤ K)
    (N : ℝ × ℝ → ℝ≥0∞) (hN : R.ReferencePopularCount u c P θ M N) :
    (Fintype.card ι : ℝ≥0∞) ≤ N ((R.referenceChart.symm z).2, z.1) := by
  classical
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hslope : ∀ i, (T i).slope ≠ R.slope := by
    intro i heq
    have h := hlower i
    rw [heq, sub_self, abs_zero] at h
    exact (not_le_of_gt hrho) h
  choose bin hbin using fun i => AngularBins.exists_baseBin R.slope hM (hslope i)
  have hinj := AngularBins.separated_annulus_bins_injective R.slope hM hB hrho hMB
    (fun i => (T i).slope) bin hsep hbin hupper
  choose F hFE hF hareaF hboxF using fun i =>
    (T i).exists_compact_popularity_witness (E i) (hE i) (hfinite i) hq (harea i) (hbox i)
  have htransfer : ∀ i, ∀ w ∈ F i,
      u (referencePoint R.slope z w) ∈ AngularBins.enlargedBin R.slope c (bin i) := by
    intro i w hw
    have hprecision' : d i ≤ |(T i).slope - R.slope| / B ^ 2 :=
      (hprecision i).trans (div_le_div_of_nonneg_right (hlower i) (sq_nonneg B))
    have herr := (T i).transferred_slope_precision R.slope z w u hu (hd i) hB0 hc0
      (hboxF i w hw) (hz i) hAK (hwidth i) hm hprecision' (hsmall i)
      (hwitness i w (hFE i hw))
    apply AngularBins.transferred_slope_mem_enlarged R.slope hM hc0 hc (hbin i)
    simpa only [hMB] using herr
  have hθ' : θ ≤ (q / 2) / (4 * A * P) := by
    convert hθ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  simpa only [Finset.card_univ] using
    R.compact_witness_list_count T Finset.univ u hu.continuous.measurable z
      hA (by positivity : 0 ≤ q / 2) hP (by linarith : A ≤ P) hθ'
      F bin (fun _ _ _ _ h => hinj h) (fun i _ => hF i)
      (fun i _ => hboxF i) (fun i _ => hareaF i) (fun i _ => hlength i)
      (fun i _ => (hz i).trans (by linarith)) (fun i _ => htransfer i) N hN

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AdmissibleListCount
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose a longest top and count the remaining directions against it. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LipschitzHilbert.SlopeBox

/-- The reference top contributes one; all other tops inject into popular
angular bins for the longest top. All reference counts are chosen in advance. -/
theorem admissible_list_card_le {ι : Type*} [DecidableEq ι]
    (T : ι → SlopeBox) (I : Finset ι) (u : ℝ × ℝ → ℝ)
    {L : ℝ≥0} (hu : LipschitzWith L u) (z : ℝ × ℝ)
    {M : ℕ} (hM : 0 < M) {A q P K θ c c0 B rho m lambda : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hP : 0 < P) (hK : 0 ≤ K)
    (hAK : A + K ≤ P) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (hθ : θ ≤ q / (8 * A * P)) (hlambda : 0 ≤ lambda)
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hfinite : ∀ i ∈ I, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i ∈ I, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i ∈ I, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i ∈ I, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i ∈ I, 0 ≤ d i)
    (hwidth : ∀ i ∈ I, (T i).width = m * (T i).length * d i)
    (hprecision : ∀ i ∈ I, d i ≤ rho / B ^ 2)
    (hsmall : ∀ i ∈ I, L * P * m * (T i).length ≤ 1 / 2)
    (hspan : ∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|)
    (hz : ∀ i ∈ I, (T i).radius z ≤ K)
    (N : ι → ℝ × ℝ → ℝ≥0∞)
    (hN : ∀ i ∈ I, (T i).ReferencePopularCount u c P θ M (N i))
    (hbound : ∀ i ∈ I, N i (((T i).referenceChart.symm z).2, z.1) ≤ ENNReal.ofReal lambda) :
    (I.card : ℝ) ≤ 1 + lambda := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨r, hr, hmax⟩ := I.exists_max_image (fun i => (T i).length) hI
    let J := {i // i ∈ I.erase r}
    have hmem (i : J) : i.val ∈ I := Finset.mem_of_mem_erase i.property
    have hne (i : J) : i.val ≠ r := (Finset.mem_erase.mp i.property).1
    have hcount := (T r).separated_witness_list_count (fun i : J => T i.val) u hu z hM
      hA hq hP hK hAK hc0 hc hB hrho hMB hm hθ
      (fun i : J => d i.val) (fun i : J => E i.val)
      (fun i => hE i.val (hmem i)) (fun i => hfinite i.val (hmem i))
      (fun i => hbox i.val (hmem i)) (fun i => harea i.val (hmem i))
      (fun i => hwitness i.val (hmem i)) (fun i => hd i.val (hmem i))
      (fun i => hwidth i.val (hmem i)) (fun i => hprecision i.val (hmem i))
      (fun i => hsmall i.val (hmem i))
      (fun i => hsep i.val (hmem i) r hr (hne i))
      (fun i => hspan i.val (hmem i) r hr)
      (fun i j hij => hsep i.val (hmem i) j.val (hmem j)
        (fun h => hij (Subtype.ext h)))
      (fun i => hmax i.val (hmem i)) (fun i => hz i.val (hmem i)) (N r) (hN r hr)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcount.trans (hbound r hr))
    have hcard : (Fintype.card J : ℝ) ≤ lambda := by
      simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlambda] using hreal
    have hJ : Fintype.card J = (I.erase r).card := Fintype.card_coe _
    have hcI := Finset.card_erase_add_one hr
    rw [hJ] at hcard
    have hcI' : ((I.erase r).card : ℝ) + 1 = I.card := by exact_mod_cast hcI
    linarith
  · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Numerical parameters for the simultaneous direction count

The final steps in §6: a fixed polynomial times a Gaussian tail is below
any prescribed exponential budget, and the chosen direction bound has
the required factor-one-hundred margin.
-/

noncomputable section

open Filter

namespace LipschitzHilbert

/-- An explicit sufficient lower bound for the count-exception budget. -/
theorem polynomial_gaussian_le_exponential {C c J a L : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hL : 1 ≤ L)
    (hlarge : (|Real.log C| + |a| + J) / c ≤ L) :
    C * L ^ a * Real.exp (-c * L ^ 2) ≤ Real.exp (-J * L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hL0]
  have hlogC : Real.log C ≤ |Real.log C| * L := by
    calc
      Real.log C ≤ |Real.log C| := le_abs_self _
      _ ≤ |Real.log C| * L := le_mul_of_one_le_right (abs_nonneg _) hL
  have haL : Real.log L * a ≤ |a| * L := by
    calc
      Real.log L * a ≤ Real.log L * |a| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hlog0
      _ ≤ L * |a| := mul_le_mul_of_nonneg_right hlogL (abs_nonneg _)
      _ = |a| * L := mul_comm _ _
  have hlinear : |Real.log C| + |a| + J ≤ c * L := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hlarge
  have hquadratic := mul_le_mul_of_nonneg_right hlinear hL0.le
  have hexponent : Real.log C + Real.log L * a + (-c * L ^ 2) ≤ -J * L := by
    nlinarith
  calc
    C * L ^ a * Real.exp (-c * L ^ 2) =
        Real.exp (Real.log C + Real.log L * a + (-c * L ^ 2)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hC, Real.rpow_def_of_pos hL0]
    _ ≤ Real.exp (-J * L) := Real.exp_le_exp.mpr hexponent

/-- `theta=L^(-a)` and `Lambda=L^(a+2)` give the exact quadratic tail. -/
theorem count_threshold_product {L : ℝ} (hL : 0 < L) (a : ℝ) :
    L ^ (-a) * L ^ (a + 2) = L ^ 2 := by
  rw [← Real.rpow_add hL]
  have heq : -a + (a + 2) = (2 : ℝ) := by ring
  rw [heq, Real.rpow_two]

/-- The manuscript's `D=L^(a+4)` absorbs the count threshold and the
reference direction with the stated factor-one-hundred margin. -/
theorem count_direction_margin {L a : ℝ} (hL : 15 ≤ L) (ha : 0 ≤ a) :
    1 + L ^ (a + 2) ≤ L ^ (a + 4) / 100 := by
  have hL0 : 0 < L := by linarith
  have hbase : 1 ≤ L ^ (a + 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hpow0 : 0 ≤ L ^ (a + 2) := Real.rpow_nonneg hL0.le _
  have hsq : 200 ≤ L ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hpow0
  have hexponent : a + 4 = (a + 2) + 2 := by ring
  have heq : L ^ (a + 4) = L ^ (a + 2) * L ^ 2 := by
    calc
      L ^ (a + 4) = L ^ ((a + 2) + 2) := by rw [hexponent]
      _ = _ := by rw [Real.rpow_add hL0, Real.rpow_two]
  rw [heq]
  nlinarith

/-- With `K=L^k`, `P=L^p`, `p≥k`, `theta=L^(-a)` and
`lambda=L^(a+2)`, the complete reference-family prefactor is absorbed
by the exact Gaussian rate supplied by angular counting. -/
theorem count_power_budget {L k p a c J : ℝ} (hL : 1 ≤ L) (hkp : k ≤ p)
    (hc : 0 ≤ c)
    (hlarge : 240 * (1 + c) * (|Real.log 768| + |2 * p| + J) ≤ L) :
    384 * L ^ k * (L ^ k + L ^ p) *
        Real.exp (-(L ^ (-a) * L ^ (a + 2)) / (240 * (1 + c))) ≤
      Real.exp (-J * L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hK : 0 ≤ L ^ k := Real.rpow_nonneg hL0.le _
  have hP : 0 ≤ L ^ p := Real.rpow_nonneg hL0.le _
  have hKP : L ^ k ≤ L ^ p := Real.rpow_le_rpow_of_exponent_le hL hkp
  have hprod : L ^ k * (L ^ k + L ^ p) ≤ 2 * (L ^ p * L ^ p) := by
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add_right hKP (L ^ p)) hK
    have h₂ := mul_le_mul_of_nonneg_right hKP (add_nonneg hP hP)
    nlinarith
  have hpower : L ^ (2 * p) = L ^ p * L ^ p := by
    rw [show 2 * p = p + p by ring, Real.rpow_add hL0]
  have hpref : 384 * L ^ k * (L ^ k + L ^ p) ≤ 768 * L ^ (2 * p) := by
    rw [hpower]
    nlinarith
  have hrate : 0 < 1 / (240 * (1 + c)) := by positivity
  have hthreshold : (|Real.log 768| + |2 * p| + J) / (1 / (240 * (1 + c))) ≤ L := by
    calc
      _ = 240 * (1 + c) * (|Real.log 768| + |2 * p| + J) := by
        rw [one_div, div_inv_eq_mul]
        ring
      _ ≤ L := hlarge
  have hbudget := polynomial_gaussian_le_exponential (C := 768) (a := 2 * p)
    (by norm_num) hrate hL hthreshold
  have hexp : -(L ^ (-a) * L ^ (a + 2)) / (240 * (1 + c)) =
      -(1 / (240 * (1 + c))) * L ^ 2 := by
    rw [count_threshold_product hL0]
    ring
  rw [hexp]
  exact (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le).trans hbudget

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountGeometryParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed powers supplying the witness dilation and popularity threshold. -/

noncomputable section

namespace LipschitzHilbert

theorem count_witness_dilation {L a k p : ℝ} (hL : 2 ≤ L)
    (ha : a + 1 ≤ p) (hk : k + 1 ≤ p) : L ^ a + L ^ k ≤ L ^ p := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ha' := Real.rpow_le_rpow_of_exponent_le hL1 (show a ≤ p - 1 by linarith)
  have hk' := Real.rpow_le_rpow_of_exponent_le hL1 (show k ≤ p - 1 by linarith)
  have hp : 0 ≤ L ^ (p - 1) := Real.rpow_nonneg hL0.le _
  have hmul := mul_le_mul_of_nonneg_right hL hp
  have heq : L ^ p = L * L ^ (p - 1) := by
    calc
      L ^ p = L ^ ((p - 1) + 1) := by congr 1; ring
      _ = L ^ (p - 1) * L := Real.rpow_add_one hL0.ne' _
      _ = _ := mul_comm _ _
  rw [heq]
  linarith

/-- One extra power of `L` absorbs the compact-extraction and interval
constants in the popularity average. -/
theorem count_popular_threshold {L a p t : ℝ} (hL : 8 ≤ L)
    (ht : 2 * a + p + 1 ≤ t) :
    L ^ (-t) ≤ L ^ (-a) / (8 * L ^ a * L ^ p) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ha : 0 < L ^ a := Real.rpow_pos_of_pos hL0 _
  have hp : 0 < L ^ p := Real.rpow_pos_of_pos hL0 _
  have hsmall := Real.rpow_le_rpow_of_exponent_le hL1
    (show -t ≤ -(2 * a + p + 1) by linarith)
  have hid : L ^ (-(2 * a + p + 1)) * (8 * L ^ a * L ^ p) =
      (8 / L) * L ^ (-a) := by
    calc
      _ = 8 * (L ^ (-(2 * a + p + 1)) * L ^ a * L ^ p) := by ring
      _ = 8 * L ^ (-(a + 1)) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
        congr 2
        ring
      _ = (8 / L) * L ^ (-a) := by
        have he : -(a + 1) = -a - 1 := by ring
        rw [he, Real.rpow_sub_one hL0.ne']
        ring
  apply hsmall.trans
  apply (le_div_iff₀ (by positivity : 0 < 8 * L ^ a * L ^ p)).mpr
  rw [hid]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hL0.le _) ((div_le_one hL0).mpr hL)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceFamilyException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The common counting exceptional set

One count is chosen for each reference top, independently of every
separated list. Their finite union has the total-top-area budget of §6.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem measurableSet_referenceFamilyException {ι : Type*} [Countable ι]
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞)
    (hN : ∀ i, Measurable (N i)) (K lambda : ℝ) :
    MeasurableSet (referenceFamilyException T N K lambda) :=
  MeasurableSet.iUnion fun i => (T i).measurableSet_referenceException (N i) (hN i) K lambda

/-- The actual exceptional union has finite measure, since each of its
reference charts is supported on a bounded rectangle. -/
theorem referenceFamilyException_measure_ne_top {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞) (K lambda : ℝ) :
    (volume.prod volume) (referenceFamilyException T N K lambda) ≠ ∞ := by
  have hsingle (i : ι) :
      (volume.prod volume) ((T i).referenceException (N i) K lambda) ≠ ∞ := by
    unfold SlopeBox.referenceException
    rw [(T i).referenceChart_image_measure]
    apply measure_ne_top_of_subset Set.inter_subset_left
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
  have hsum : (∑ i, (volume.prod volume) ((T i).referenceException (N i) K lambda)) < ∞ :=
    ENNReal.sum_lt_top.mpr (fun i _ => (hsingle i).lt_top)
  exact ((measure_iUnion_fintype_le _ _).trans_lt hsum).ne

/-- Outside the single union, every significant reference has its count
bounded by the same threshold. -/
theorem count_le_outside_referenceFamilyException {ι : Type*}
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞) {K lambda : ℝ}
    {z : ℝ × ℝ} (hout : z ∉ referenceFamilyException T N K lambda)
    (i : ι) (hsignificant : (T i).radius z ≤ K) :
    N i (((T i).referenceChart.symm z).2, z.1) ≤ ENNReal.ofReal lambda := by
  apply (T i).count_le_outside_referenceException (N i) hsignificant
  intro hi
  exact hout (Set.mem_iUnion.mpr ⟨i, hi⟩)

theorem referenceFamilyException_measure_bound {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞) {K P θ c lambda : ℝ}
    (hbound : ∀ i,
      (volume.prod volume).real ((T i).referenceException (N i) K lambda) ≤
        384 * K * (K + P) * (T i).length * (T i).width *
          Real.exp (-θ * lambda / (240 * (1 + c)))) :
    (volume.prod volume).real (referenceFamilyException T N K lambda) ≤
      (∑ i, (T i).length * (T i).width) *
        (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) := by
  calc
    _ ≤ ∑ i, (volume.prod volume).real ((T i).referenceException (N i) K lambda) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, ((T i).length * (T i).width) *
        (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) := by
      apply Finset.sum_le_sum
      intro i _
      convert hbound i using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = _ := (Finset.sum_mul ..).symm

/-- Actual reference counts exist simultaneously for the finite top
family. The counts are fixed before the threshold and before the list. -/
theorem reference_family_count_setup {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    {M : ℕ} (hM : 0 < M) {c K P θ : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M)
    (hK : 0 ≤ K) (hP : 0 < P) (hθ : 0 < θ) :
    ∃ N : ι → ℝ × ℝ → ℝ≥0∞, (∀ i, Measurable (N i)) ∧
      (∀ i, (T i).ReferencePopularCount u c P θ M (N i)) ∧
      ∀ lambda : ℝ, 0 ≤ lambda →
        MeasurableSet (referenceFamilyException T N K lambda) ∧
        (volume.prod volume).real (referenceFamilyException T N K lambda) ≤
          (∑ i, (T i).length * (T i).width) *
            (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) := by
  classical
  choose N hN hpopular htail using
    (fun i => (T i).reference_count_setup u hu hM hc hcM hK hP hθ)
  refine ⟨N, hN, hpopular, ?_⟩
  intro lambda hlambda
  exact ⟨measurableSet_referenceFamilyException T N hN K lambda,
    referenceFamilyException_measure_bound T N (fun i => htail i lambda hlambda)⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTimeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source cutoff beats the enlarged width and every fixed polynomial. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

/-- The two exponents are exactly the manuscript's `0.9` and `0.97`.
This is the numerical small-time input to compact-witness transfer. -/
theorem eventually_short_time_decay (p : ℝ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,
      2 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 1 / 2 := by
  have hlog := (isLittleO_log_rpow_atTop (r := 97 / 100) (by norm_num)).const_mul_left p
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 100)).eventually_ge_atTop 3,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 97 / 100)).eventually_ge_atTop
      (3 * |Real.log (4 * C)|),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 3)] with L hL hgap hconstant hlogL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr : 0 ≤ L ^ (97 / 100 : ℝ) := Real.rpow_nonneg hL0.le _
  have hs : 0 ≤ L ^ (9 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  simp only [Real.norm_eq_abs, abs_of_nonneg hr] at hlogL
  have hpower : L ^ (97 / 100 : ℝ) = L ^ (9 / 10 : ℝ) * L ^ (7 / 100 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hslow : 3 * L ^ (9 / 10 : ℝ) ≤ L ^ (97 / 100 : ℝ) := by
    rw [hpower]
    nlinarith [mul_le_mul_of_nonneg_left hgap hs]
  have hexponent : Real.log (4 * C) + Real.log L * p +
      (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 0 := by
    have hlogabs := le_abs_self (p * Real.log L)
    have hcabs := le_abs_self (Real.log (4 * C))
    nlinarith
  have hfour : 4 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 1 := by
    calc
      _ = Real.exp (Real.log (4 * C) + Real.log L * p +
          (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity : 0 < 4 * C),
          Real.rpow_def_of_pos hL0]
      _ ≤ 1 := Real.exp_le_one_iff.mpr hexponent
  nlinarith

/-- The actual source inequalities `m≤2 exp(L^0.9)` and
`tau≤exp(-L^0.97)` imply the exact transfer hypothesis uniformly over
all top lengths below `tau`. -/
theorem eventually_transfer_small_time (p : ℝ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ m tau ell : ℝ,
      0 ≤ m → m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      0 ≤ ell → ell ≤ tau → C * L ^ p * m * ell ≤ 1 / 2 := by
  by_cases hzero : C = 0
  · subst C
    exact Filter.Eventually.of_forall (by intros; norm_num)
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  filter_upwards [eventually_short_time_decay p hCpos, eventually_ge_atTop (0 : ℝ)]
    with L hdecay hL m tau ell hm hmb ht htb he heb
  have hLp : 0 ≤ L ^ p := Real.rpow_nonneg hL _
  calc
    C * L ^ p * m * ell ≤ C * L ^ p * m * tau :=
      mul_le_mul_of_nonneg_left heb (by positivity)
    _ ≤ C * L ^ p * (2 * Real.exp (L ^ (9 / 10 : ℝ))) *
        Real.exp (-(L ^ (97 / 100 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmb (by positivity)) htb ht (by positivity)
    _ = 2 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ 1 / 2 := hdecay

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SimultaneousCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One exceptional set for all separated significant-direction lists. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

/-- Quantitative simultaneous counting from the original measurable
popularity witnesses. The exceptional set is chosen before the point,
separation scale, and list, and costs only total top area. -/
theorem simultaneous_separated_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u)
    {M : ℕ} (hM : 0 < M) {A q P K θ c c0 B m lambda : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hP : 0 < P) (hK : 0 ≤ K)
    (hAK : A + K ≤ P) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hcM : c ≤ M) (hB : 1 < B) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (hθ0 : 0 < θ) (hθ : θ ≤ q / (8 * A * P)) (hlambda : 0 ≤ lambda)
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i, 0 ≤ d i) (hwidth : ∀ i, (T i).width = m * (T i).length * d i)
    (hsmall : ∀ i, L * P * m * (T i).length ≤ 1 / 2) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
      (volume.prod volume).real bad ≤
        (∑ i, (T i).length * (T i).width) *
          (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) ∧
      ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
        (∀ i ∈ I, (T i).radius z ≤ K) →
        (∀ i ∈ I, d i ≤ rho / B ^ 2) →
        (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
        (I.card : ℝ) ≤ 1 + lambda := by
  have hc0' : 0 ≤ c := by linarith
  obtain ⟨N, _, hN, htail⟩ := reference_family_count_setup T u hu.continuous.measurable
    hM hc0' hcM hK hP hθ0
  obtain ⟨hmeas, hmeasure⟩ := htail lambda hlambda
  refine ⟨referenceFamilyException T N K lambda, hmeas,
    referenceFamilyException_measure_ne_top T N K lambda, hmeasure, ?_⟩
  intro z hz rho hrho I hsignificant hprecision hspan hsep
  apply SlopeBox.admissible_list_card_le T I u hu z hM hA hq hP hK hAK hc0 hc
    hB hrho hMB hm hθ hlambda d E
    (fun i _ => hE i) (fun i _ => hfinite i) (fun i _ => hbox i)
    (fun i _ => harea i) (fun i _ => hwitness i) (fun i _ => hd i)
    (fun i _ => hwidth i) hprecision (fun i _ => hsmall i) hspan hsep hsignificant
    N (fun i _ => hN i)
  exact fun i hi => count_le_outside_referenceFamilyException T N hz i (hsignificant i hi)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SimultaneousCountPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous count at the manuscript's polynomial thresholds. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

/-- The finite-family version of §6's simultaneous-count proposition:
an `S exp(-J L)` exceptional set and the uniform `D/100` list bound.
The small-time hypothesis is stated in the precise strength used by
the proved Lipschitz transfer, and all numerical choices are explicit. -/
theorem simultaneous_separated_count_powers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ) {Lip : ℝ≥0} (hu : LipschitzWith Lip u)
    {L a k p t c c0 B m J : ℝ} {M : ℕ}
    (hL : 15 ≤ L) (ha : 0 ≤ a)
    (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p) (ht : 2 * a + p + 1 ≤ t)
    (hlarge : 240 * (1 + c) * (|Real.log 768| + |2 * p| + J) ≤ L)
    (hM : 0 < M) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hcM : c ≤ M) (hB : 1 < B) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a)
    (harea : ∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i, 0 ≤ d i) (hwidth : ∀ i, (T i).width = m * (T i).length * d i)
    (hsmall : ∀ i, Lip * L ^ p * m * (T i).length ≤ 1 / 2) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
      (volume.prod volume).real bad ≤
        (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
      ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
        (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
        (∀ i ∈ I, d i ≤ rho / B ^ 2) →
        (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
        (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hc' : 0 ≤ c := by linarith
  obtain ⟨bad, hmeas, hfiniteBad, hmeasure, hcount⟩ := simultaneous_separated_count T u hu hM
    (Real.rpow_pos_of_pos hL0 a) (Real.rpow_pos_of_pos hL0 (-a))
    (Real.rpow_pos_of_pos hL0 p) (Real.rpow_nonneg hL0.le k)
    (count_witness_dilation (by linarith) hap hkp) hc0 hc hcM hB hMB hm
    (Real.rpow_pos_of_pos hL0 (-t)) (count_popular_threshold (by linarith) ht)
    (Real.rpow_nonneg hL0.le (t + 2)) d E hE hfinite hbox harea hwitness hd hwidth hsmall
  refine ⟨bad, hmeas, hfiniteBad, ?_, ?_⟩
  · have hbudget := count_power_budget (a := t) hL1 (by linarith : k ≤ p) hc' hlarge
    have hbudget' : 384 * L ^ k * (L ^ k + L ^ p) *
        Real.exp (-(L ^ (-t)) * L ^ (t + 2) / (240 * (1 + c))) ≤ Real.exp (-J * L) := by
      simpa only [neg_mul] using hbudget
    exact hmeasure.trans (mul_le_mul_of_nonneg_left hbudget'
      (Finset.sum_nonneg fun i _ => mul_nonneg (T i).length_pos.le (T i).width_pos.le))
  · intro z hz rho hrho I hsignificant hprecision hspan hsep
    exact (hcount z hz rho hrho I hsignificant hprecision hspan hsep).trans
      (count_direction_margin hL (by linarith : 0 ≤ t))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem branchingNat_cast (L : ℝ) : (branchingNat L : ℝ) = branching L := by
  simp only [branchingNat, branching, step, Nat.cast_pow, Nat.cast_ofNat]

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

theorem log_branching_le {L : ℝ} (hL : 0 ≤ L) :
    Real.log (branching L) ≤
      (Real.log L ^ 2 + 1) * (L ^ (7 / 10 : ℝ) + 2 * Real.log 2) := by
  rw [branching, Real.log_pow]
  have hK : (blockCount L : ℝ) ≤ Real.log L ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact mul_le_mul hK (log_step_bounds hL).2
    (Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)

/-- The actual rounded dyadic branching satisfies the scale separation
`B^100 ≤ exp(L^0.9)` eventually, with no real-valued stand-in for `B`. -/
theorem eventually_branching_separation :
    ∀ᶠ L : ℝ in atTop, branching L ^ 100 ≤ Real.exp (L ^ (9 / 10 : ℝ)) := by
  have hlog := isLittleO_log_rpow_rpow_atTop (r := 2) (s := 1 / 5) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop (2 * Real.log 2),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 400)] with L hL hlogL hpow hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp7 : 0 ≤ L ^ (7 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp2 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlogsq : 1 ≤ Real.log L ^ 2 := by nlinarith
  rw [Real.rpow_two] at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hp2] at hsmall
  have hcrude : Real.log (branching L) ≤ 4 * L ^ (7 / 10 : ℝ) * Real.log L ^ 2 := by
    apply (log_branching_le hL0.le).trans
    nlinarith [mul_le_mul (show Real.log L ^ 2 + 1 ≤ 2 * Real.log L ^ 2 by linarith)
      (show L ^ (7 / 10 : ℝ) + 2 * Real.log 2 ≤ 2 * L ^ (7 / 10 : ℝ) by linarith)
      (by positivity : 0 ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2)
      (by positivity : 0 ≤ 2 * Real.log L ^ 2)]
  have hpower : L ^ (7 / 10 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hbound : 100 * Real.log (branching L) ≤ L ^ (9 / 10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) hp7)
    nlinarith
  calc
    branching L ^ 100 = Real.exp (100 * Real.log (branching L)) := by
      have heq : Real.log (branching L ^ (100 : ℕ)) = (100 : ℝ) * Real.log (branching L) := by
        simpa only [Nat.cast_ofNat] using (Real.log_pow (branching L) 100)
      rw [← heq, Real.exp_log (pow_pos (branching_pos L) _)]
    _ ≤ Real.exp (L ^ (9 / 10 : ℝ)) := Real.exp_le_exp.mpr hbound

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCountParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dyadic source parameters meet the counting hypotheses. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem blockCount_pos {L : ℝ} (hL : 1 < L) : 0 < blockCount L := by
  apply Nat.one_le_ceil_iff.mpr
  exact sq_pos_of_pos (Real.log_pos hL)

theorem one_lt_step {L : ℝ} (hL : 0 < L) : 1 < step L := by
  apply (Real.log_pos_iff (step_pos L).le).mp
  exact (Real.rpow_pos_of_pos hL _).trans_le (log_step_bounds hL.le).1

theorem one_lt_branching {L : ℝ} (hL : 1 < L) : 1 < branching L :=
  one_lt_pow₀ (one_lt_step (zero_lt_one.trans hL)) (Nat.ne_of_gt (blockCount_pos hL))

theorem log_branching_lower {L : ℝ} (hL : 1 < L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (branching L) := by
  have hstep := one_lt_step (zero_lt_one.trans hL)
  have hK : (1 : ℝ) ≤ blockCount L := by exact_mod_cast blockCount_pos hL
  calc
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) := (log_step_bounds (zero_lt_one.trans hL).le).1
    _ ≤ (blockCount L : ℝ) * Real.log (step L) :=
      le_mul_of_one_le_left (Real.log_nonneg hstep.le) hK
    _ = Real.log (branching L) := (Real.log_pow _ _).symm

theorem eventually_branching_ge (c : ℝ) : ∀ᶠ L : ℝ in atTop, c ≤ branching L := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop
      (Real.log (max c 1))] with L hL hpow
  have hmax : 0 < max c 1 := zero_lt_one.trans_le (le_max_right _ _)
  apply (le_max_left c 1).trans
  exact (Real.log_le_log_iff hmax (branching_pos L)).mp
    (hpow.trans (log_branching_lower (by linarith)))

/-- For every fixed enlargement and polynomial, the actual integer bin
count and the manuscript's width/cutoff scales satisfy all numerical
conditions used in the simultaneous count. -/
theorem eventually_count_parameters (p c C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      1 < branching L ∧ 0 < (branchingNat L) ^ 2 ∧
      c ≤ ((branchingNat L) ^ 2 : ℕ) ∧
      (((branchingNat L) ^ 2 : ℕ) : ℝ) = branching L ^ 2 ∧
      ∀ m tau : ℝ,
        Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
        m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
        0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
        branching L ^ 2 ≤ m ∧
        ∀ ell : ℝ, 0 ≤ ell → ell ≤ tau → C * L ^ p * m * ell ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_branching_ge c,
    eventually_branching_separation, LipschitzHilbert.eventually_transfer_small_time p C hC]
    with L hL hc hsep htime
  have hB : 1 < branching L := one_lt_branching (by linarith)
  have hBN : 0 < branchingNat L := by
    have : (0 : ℝ) < branchingNat L := by rw [branchingNat_cast]; exact branching_pos L
    exact_mod_cast this
  have hcast : (((branchingNat L) ^ 2 : ℕ) : ℝ) = branching L ^ 2 := by
    rw [Nat.cast_pow, branchingNat_cast]
  have hBsq : branching L ≤ branching L ^ 2 := le_self_pow₀ hB.le (by norm_num)
  refine ⟨hB, pow_pos hBN _, ?_, hcast, ?_⟩
  · rw [hcast]
    exact hc.trans hBsq
  · intro m tau hml hmu ht htu
    have hm : 0 ≤ m := (Real.exp_pos _).le.trans hml
    refine ⟨(pow_le_pow_right₀ hB.le (by norm_num : 2 ≤ 100)).trans (hsep.trans hml), ?_⟩
    exact fun ell he het => htime m tau ell hm hmu ht htu he het

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSimultaneousCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous-count proposition for the manuscript's actual scales. -/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

/-- The lower threshold for `L` is independent of the finite top family.
The dyadic branching parameter, enlarged width, and short-time cutoff are
the original manuscript choices. No extra counting or transfer estimate
is assumed. -/
theorem eventually_source_simultaneous_count_universal_oai (Lip : ℝ≥0)
    (a k p t c c0 J : ℝ) (ha : 0 ≤ a) (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p)
    (ht : 2 * a + p + 1 ≤ t) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (u : ℝ × ℝ → ℝ), LipschitzWith Lip u →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], ∀ m tau : ℝ,
      Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
      m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      ∀ (T : ι → SlopeBox) (d : ι → ℝ) (E : ι → Set (ℝ × ℝ)),
        (∀ i, (T i).length ≤ tau) →
        (∀ i, MeasurableSet (E i)) →
        (∀ i, (volume.prod volume) (E i) ≠ ∞) →
        (∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a) →
        (∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i)) →
        (∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i) →
        (∀ i, 0 ≤ d i) → (∀ i, (T i).width = m * (T i).length * d i) →
        ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
          (volume.prod volume).real bad ≤
            (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
          ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
            (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
            (∀ i ∈ I, d i ≤ rho / SourceParameters.branching L ^ 2) →
            (∀ i ∈ I, ∀ j ∈ I,
              |(T i).slope - (T j).slope| ≤ SourceParameters.branching L * rho) →
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
            (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  filter_upwards [eventually_ge_atTop (15 : ℝ),
    eventually_ge_atTop (240 * (1 + c) * (|Real.log 768| + |2 * p| + J)),
    SourceParameters.eventually_count_parameters p c Lip Lip.coe_nonneg]
    with L hL hlarge hparameters
  intro u hu ι _ _ m tau hml hmu hta htau T d E hlength hE hfinite hbox harea hwitness hd hwidth
  obtain ⟨hB, hM, hcM, hMB, hscales⟩ := hparameters
  obtain ⟨hm, hsmall⟩ := hscales m tau hml hmu hta htau
  exact simultaneous_separated_count_powers T u hu hL ha hap hkp ht hlarge hM hc0 hc hcM
    hB hMB hm d E hE hfinite hbox harea hwitness hd hwidth
    (fun i => hsmall (T i).length (T i).length_pos.le (hlength i))

end LipschitzHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal_oai.{u_1} := @OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal_oai.{u_1}
