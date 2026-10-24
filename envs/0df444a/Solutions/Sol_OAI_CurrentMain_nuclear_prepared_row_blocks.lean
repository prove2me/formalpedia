-- Prove2me | solution 1 for OAI.CurrentMain.nuclear_prepared_row_blocks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:14:23.690858+00:00
-- url     : https://prove2.me/submissions/5fc329b1-0267-4fe0-98ac-6f0429526b3e

import Mathlib
import Definitions.Def_UniformGamma
import Definitions.Def_OAIQWCMM000

section
-- module Solutions.OAIQW_TracialSplitting.Compat
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
-- module Solutions.OAIQW_TracialSplitting.TraceEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section TraceIdentities

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D]

lemma trace_projection_corner (τ : TracialState D) {p : D}
    (hp : IsStarProjection p) (a : D) :
    τ.functional (p * a * p) = τ.functional (p * a) := by
  rw [τ.tracial (p * a) p, ← mul_assoc, hp.isIdempotentElem]

lemma trace_unitary_conjugate (τ : TracialState D) (x : unitary D) (a : D) :
    τ.functional ((x : D) * a * star (x : D)) = τ.functional a := by
  rw [τ.tracial ((x : D) * a) (star (x : D))]
  simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul]

end TraceIdentities

section TraceBounds

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sq (τ : TracialState D) (a : D) :
    traceTwoNorm τ a ^ 2 = (τ.functional (star a * a)).re := by
  exact Real.sq_sqrt (τ.functional.map_nonneg (star_mul_self_nonneg a)).1

lemma traceTwoNorm_smul (τ : TracialState D) (z : ℂ) (a : D) :
    traceTwoNorm τ (z • a) = ‖z‖ * traceTwoNorm τ a := by
  simp only [traceTwoNorm_eq_gns, map_smul, norm_smul]

lemma trace_norm_mul_le (τ : TracialState D) (a b : D) :
    ‖τ.functional (a * b)‖ ≤ traceTwoNorm τ a * traceTwoNorm τ b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.functional.toPreGNS (star a))
    (τ.functional.toPreGNS b)
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_star,
    ← traceTwoNorm_eq_gns, traceTwoNorm_star] using h

end TraceBounds

section WeightedAveraging

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype I]

lemma weightedAverage_nonneg (w : I → ℝ) (v : I → D)
    (hw : ∀ i, 0 ≤ w i) {b : D} (hb : 0 ≤ b) :
    0 ≤ weightedAverage w v b := by
  exact Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (star_right_conjugate_nonneg hb (v i))

end WeightedAveraging

section PowersStormer

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceOneNorm_nonneg (τ : TracialState D) (a : D) : 0 ≤ traceOneNorm τ a :=
  (τ.functional.map_nonneg (CFC.abs_nonneg a)).1

lemma trace_square_sub_le_abs (τ : TracialState D) {u v : D}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (τ.functional ((u - v) * (u - v))).re ≤
      (τ.functional ((u + v) * CFC.abs (u - v))).re := by
  have hd : IsSelfAdjoint (u - v) := (IsSelfAdjoint.of_nonneg hu).sub
    (IsSelfAdjoint.of_nonneg hv)
  have hp := (trace_mul_nonneg τ (add_nonneg hv hv) (CFC.posPart_nonneg (u - v))).1
  have hn := (trace_mul_nonneg τ (add_nonneg hu hu) (CFC.negPart_nonneg (u - v))).1
  have he : (v + v) * (u - v)⁺ + (u + u) * (u - v)⁻ =
      (u + v) * CFC.abs (u - v) - (u - v) * (u - v) := by
    rw [← CFC.posPart_add_negPart (u - v) hd]
    have hde := CFC.posPart_sub_negPart (u - v) hd
    calc
      _ = (u + v) * ((u - v)⁺ + (u - v)⁻) -
          (u - v) * ((u - v)⁺ - (u - v)⁻) := by noncomm_ring
      _ = _ := by rw [hde]
  have he' := congrArg (fun a => (τ.functional a).re) he
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re] at he'
  simp only [Complex.zero_re] at hp hn
  linarith

omit [PartialOrder D] [StarOrderedRing D] in
lemma regularizedSign_commute (ε : ℝ) {d : D} (hd : IsSelfAdjoint d) :
    Commute (regularizedSign ε d) d :=
  hd.commute_cfc (.refl d) _

omit [StarOrderedRing D] in
lemma trace_square_difference_sign (τ : TracialState D) (u v s : D)
    (hcomm : Commute s (u - v)) :
    τ.functional (s * (u * u - v * v)) =
      τ.functional ((u + v) * s * (u - v)) := by
  have he : s * (u * u - v * v) =
      s * u * (u - v) + s * (u - v) * v := by noncomm_ring
  have ht : τ.functional (s * u * (u - v)) =
      τ.functional (u * s * (u - v)) := by
    rw [τ.tracial (s * u) (u - v), ← mul_assoc, ← hcomm.eq,
      τ.tracial (s * (u - v)) u, mul_assoc]
  rw [he, map_add, ht, τ.tracial (s * (u - v)) v, ← map_add]
  congr 1
  noncomm_ring

lemma trace_square_sub_le_oneNorm (τ : TracialState D) {u v : D}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (τ.functional ((u - v) * (u - v))).re ≤ traceOneNorm τ (u * u - v * v) := by
  have hd : IsSelfAdjoint (u - v) := (IsSelfAdjoint.of_nonneg hu).sub
    (IsSelfAdjoint.of_nonneg hv)
  have hh : IsSelfAdjoint (u * u - v * v) := by
    change star (u * u - v * v) = _
    simp only [star_sub, star_mul, hu.star_eq, hv.star_eq]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ / (‖u + v‖ + 1)
  have hepos : 0 < ε := div_pos hδ (by positivity)
  let s := regularizedSign ε (u - v)
  have hs := regularizedSign_selfAdjoint ε (u - v)
  have hsb := trace_selfAdjoint_contraction_mul_le τ hs hh (regularizedSign_norm_le hepos _)
  have hre := congrArg Complex.re (trace_square_difference_sign τ u v s
    (regularizedSign_commute ε hd))
  have hnear : (τ.functional ((u + v) * CFC.abs (u - v))).re -
      (τ.functional ((u + v) * s * (u - v))).re ≤ ‖u + v‖ * ε := by
    calc
      _ = (τ.functional ((u + v) * (CFC.abs (u - v) - s * (u - v)))).re := by
        simp only [mul_sub, map_sub, Complex.sub_re, mul_assoc]
      _ ≤ ‖τ.functional ((u + v) * (CFC.abs (u - v) - s * (u - v)))‖ :=
        Complex.re_le_norm _
      _ ≤ ‖(u + v) * (CFC.abs (u - v) - s * (u - v))‖ := trace_norm_le_norm τ _
      _ ≤ ‖u + v‖ * ‖CFC.abs (u - v) - s * (u - v)‖ := norm_mul_le _ _
      _ ≤ ‖u + v‖ * ε := mul_le_mul_of_nonneg_left (regularizedSign_error hepos hd)
        (norm_nonneg _)
  have heδ : ‖u + v‖ * ε ≤ δ := by
    have ht : (‖u + v‖ + 1) * ε = δ := by
      dsimp [ε]
      field_simp
    nlinarith [norm_nonneg (u + v)]
  have hl := trace_square_sub_le_abs τ hu hv
  linarith

theorem powers_stormer (τ : TracialState D) {b c : D} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    traceTwoNorm τ (CFC.sqrt b - CFC.sqrt c) ^ 2 ≤ traceOneNorm τ (b - c) := by
  have h := trace_square_sub_le_oneNorm τ (CFC.sqrt_nonneg b) (CFC.sqrt_nonneg c)
  rw [CFC.sqrt_mul_sqrt_self b hb, CFC.sqrt_mul_sqrt_self c hc] at h
  rw [traceTwoNorm_sq, ((CFC.sqrt_nonneg b).isSelfAdjoint.sub
    (CFC.sqrt_nonneg c).isSelfAdjoint).star_eq]
  exact h

end PowersStormer

section ProjectiveAveraging

open scoped TensorProduct

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_projection_sq (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) : traceTwoNorm τ q ^ 2 = (τ.functional q).re := by
  rw [traceTwoNorm_sq, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem]

lemma trace_sandwich_pairing_le (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (s a b : D) :
    ‖τ.functional (s * a * q * b)‖ ≤
      ‖s‖ * (τ.functional q).re * (‖a‖ * ‖b‖) := by
  have heq : s * a * q * b = ((s * a) * q) * (q * b) := by
    simp only [mul_assoc]
    rw [← mul_assoc q q b, hq.isIdempotentElem]
  have hq0 := traceTwoNorm_nonneg τ q
  calc
    _ ≤ traceTwoNorm τ ((s * a) * q) * traceTwoNorm τ (q * b) := by
      rw [heq]; exact trace_norm_mul_le τ _ _
    _ ≤ (‖s * a‖ * traceTwoNorm τ q) * (‖b‖ * traceTwoNorm τ q) :=
      mul_le_mul (traceTwoNorm_mul_left τ _ _) (traceTwoNorm_mul_right τ _ _)
        (traceTwoNorm_nonneg τ _) (by positivity)
    _ ≤ (‖s‖ * ‖a‖ * traceTwoNorm τ q) * (‖b‖ * traceTwoNorm τ q) := by
      gcongr; exact norm_mul_le _ _
    _ = ‖s‖ * (τ.functional q).re * (‖a‖ * ‖b‖) := by
      rw [← traceTwoNorm_projection_sq τ hq]; ring

end ProjectiveAveraging

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FiniteSpectralResolution

variable {D : Type uD} [CStarAlgebra D]

lemma realSpectrum_finite {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℂ a).Finite) : (spectrum ℝ a).Finite := by
  rw [← ha.spectrumRestricts.image]
  exact hfinite.image _

lemma spectralAtom_eigenvalue {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) (t : ℝ) : a * spectralAtom a t = t • spectralAtom a t := by
  change a * cfc (fun x : ℝ => if x = t then (1 : ℝ) else 0) a =
    t • cfc (fun x : ℝ => if x = t then (1 : ℝ) else 0) a
  nth_rw 1 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a continuous_id.continuousOn (hfinite.continuousOn _),
    ← cfc_smul _ _ a (hfinite.continuousOn _)]
  apply cfc_congr
  intro x _
  by_cases hxt : x = t <;> simp [hxt]

end FiniteSpectralResolution

section ProjectionCorners

variable {D : Type uD} [CStarAlgebra D]

namespace ProjectionCorner

variable {p : D} (hp : IsStarProjection p)

lemma inclusion_isometric : Isometry (inclusion hp) := fun _ _ => rfl

lemma isSelfAdjoint_coe {a : ProjectionCorner hp} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (a : D) := congrArg Subtype.val ha

lemma coe_cfc {a : ProjectionCorner hp} (ha : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    ((cfc f a : ProjectionCorner hp) : D) = cfc f (a : D) := by
  rw [← cfcₙ_eq_cfc hf.continuousOn hf0, ← cfcₙ_eq_cfc hf.continuousOn hf0]
  exact (inclusion hp).map_cfcₙ f a hf.continuousOn hf0
    (inclusion_isometric hp).continuous ha (isSelfAdjoint_coe hp ha)

lemma spectrum_coe_subset (a : ProjectionCorner hp) :
    spectrum ℝ (a : D) ⊆ spectrum ℝ a ∪ {0} := by
  apply Set.Subset.trans (spectrum_subset_quasispectrum ℝ (a : D))
  rw [← quasispectrum_eq_spectrum_union_zero]
  exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ (inclusion hp) a

lemma spectrum_subset_coe (a : ProjectionCorner hp) :
    spectrum ℂ a ⊆ spectrum ℂ (a : D) := by
  intro t ht
  rw [spectrum.mem_iff] at ht ⊢
  intro hu
  obtain ⟨u, hu⟩ := hu
  let x : ProjectionCorner hp := algebraMap ℂ (ProjectionCorner hp) t - a
  have hx : (x : D) = p * (u : D) := by
    rw [hu]
    change t • p - (a : D) = p * (algebraMap ℂ D t - (a : D))
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, a.property.1]
  have hx' : (x : D) = (u : D) * p := by
    rw [hu]
    change t • p - (a : D) = (algebraMap ℂ D t - (a : D)) * p
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, a.property.2]
  apply ht
  refine ⟨⟨x, compress hp (u⁻¹ : Dˣ), ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change (x : D) * (p * (↑u⁻¹ : D) * p) = p
    rw [← mul_assoc (x : D) _ p, ← mul_assoc (x : D) p, x.property.2, hx,
      mul_assoc p, Units.mul_inv, mul_one, hp.isIdempotentElem.eq]
  · apply Subtype.ext
    change p * (↑u⁻¹ : D) * p * (x : D) = p
    rw [mul_assoc, x.property.1, hx', ← mul_assoc, mul_assoc p, Units.inv_mul,
      mul_one, hp.isIdempotentElem.eq]

lemma finite_spectrum_of_coe {a : ProjectionCorner hp} (ha : (spectrum ℂ (a : D)).Finite) :
    (spectrum ℂ a).Finite := ha.subset (spectrum_subset_coe hp a)

end ProjectionCorner

end ProjectionCorners

section ProjectionPolars

open scoped NNReal

open Topology

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma unitaryPolar_mem {z : D} (hz : IsUnit z) : unitaryPolar z ∈ unitary D := by
  let s := CFC.sqrt (star z * z)
  have hs : IsUnit s := (CFC.isUnit_sqrt_iff _).mpr (hz.star.mul hz)
  have hss : s * s = star z * z := CFC.sqrt_mul_sqrt_self _
  have hsa : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hsi : star (Ring.inverse s) = Ring.inverse s := by
    rw [← Ring.inverse_star, hsa]
  have hleft : star (unitaryPolar z) * unitaryPolar z = 1 := by
    change star (z * Ring.inverse s) * (z * Ring.inverse s) = 1
    rw [star_mul, hsi]
    calc
      _ = Ring.inverse s * (star z * z) * Ring.inverse s := by simp only [mul_assoc]
      _ = Ring.inverse s * (s * s) * Ring.inverse s := by rw [hss]
      _ = 1 := by rw [← mul_assoc, Ring.inverse_mul_cancel s hs, one_mul,
        Ring.mul_inverse_cancel s hs]
  have hu : IsUnit (unitaryPolar z) := hz.mul (hs.ringInverse)
  exact ⟨hleft, hu.mul_left_inj.mp (by simp only [mul_assoc, hleft, mul_one, one_mul])⟩

lemma continuousAt_unitaryPolar_one : ContinuousAt (unitaryPolar : D → D) 1 := by
  have hs : Continuous (fun z : D => CFC.sqrt (star z * z)) :=
    CFC.continuousOn_sqrt.comp_continuous (continuous_star.mul continuous_id)
      (fun z => star_mul_self_nonneg z)
  have hi : ContinuousAt (fun z : D => Ring.inverse (CFC.sqrt (star z * z))) 1 := by
    apply ContinuousAt.comp (g := Ring.inverse) (f := fun z : D => CFC.sqrt (star z * z))
    · simpa using (NormedRing.inverse_continuousAt (1 : Dˣ))
    · exact hs.continuousAt
  exact continuousAt_id.mul hi

omit [PartialOrder D] [StarOrderedRing D] in
lemma commute_ring_inverse {a b : D} (h : Commute a b) (ha : IsUnit a) :
    Commute (Ring.inverse a) b := by
  apply ha.mul_right_inj.mp
  change a * (Ring.inverse a * b) = a * (b * Ring.inverse a)
  rw [← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul, ← mul_assoc, h.eq,
    mul_assoc, Ring.mul_inverse_cancel a ha, mul_one]

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_self {p : D} (hp : IsStarProjection p) :
    projectionIntertwiner p p = 1 := by
  have hpp : p * p = p := hp.isIdempotentElem
  simp only [projectionIntertwiner, sub_mul, mul_sub, one_mul, mul_one, hpp]
  abel

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_mul {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : projectionIntertwiner p q * q = p * projectionIntertwiner p q := by
  have hpp : p * p = p := hp.isIdempotentElem
  have hqq : q * q = q := hq.isIdempotentElem
  have hz : projectionIntertwiner p q = 1 - p - q + 2 • (p * q) := by
    dsimp [projectionIntertwiner]
    noncomm_ring
  rw [hz]
  simp only [add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm]
  rw [mul_assoc p q q, hqq, ← mul_assoc p p q, hpp]
  abel

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_star {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : star (projectionIntertwiner p q) = projectionIntertwiner q p := by
  simp [projectionIntertwiner, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

omit [PartialOrder D] [StarOrderedRing D] in
lemma projectionIntertwiner_square_commute {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    Commute (star (projectionIntertwiner p q) * projectionIntertwiner p q) q := by
  rw [projectionIntertwiner_star hp hq]
  show projectionIntertwiner q p * projectionIntertwiner p q * q =
    q * (projectionIntertwiner q p * projectionIntertwiner p q)
  rw [mul_assoc, projectionIntertwiner_mul hp hq, ← mul_assoc,
    projectionIntertwiner_mul hq hp, mul_assoc]

lemma unitaryPolar_intertwines {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hz : IsUnit (projectionIntertwiner p q)) :
    unitaryPolar (projectionIntertwiner p q) * q =
      p * unitaryPolar (projectionIntertwiner p q) := by
  let z := projectionIntertwiner p q
  have hs : Commute (CFC.sqrt (star z * z)) q :=
    (projectionIntertwiner_square_commute hp hq).cfcₙ_nnreal NNReal.sqrt
  have hi := commute_ring_inverse hs ((CFC.isUnit_sqrt_iff _).mpr (hz.star.mul hz))
  change z * Ring.inverse (CFC.sqrt (star z * z)) * q =
    p * (z * Ring.inverse (CFC.sqrt (star z * z)))
  rw [mul_assoc, hi.eq, ← mul_assoc, projectionIntertwiner_mul hp hq, mul_assoc]

end ProjectionPolars

section SpectralCutoffs

variable {D : Type uD} [CStarAlgebra D]

lemma gapCutoff_continuous : Continuous gapCutoff := by
  unfold gapCutoff
  fun_prop

lemma gapCutoff_eq_zero {t : ℝ} (h : t ≤ 1) : gapCutoff t = 0 := by
  unfold gapCutoff
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

lemma gapCutoff_eq_one {t : ℝ} (h : 2 ≤ t) : gapCutoff t = 1 := by
  unfold gapCutoff
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

@[simp] lemma gapCutoff_zero : gapCutoff 0 = 0 := gapCutoff_eq_zero (by norm_num)

lemma spectralCut_isProjection {a : D}
    (hgap : ∀ t ∈ spectrum ℝ a, t ≤ 1 ∨ 2 ≤ t) :
    IsStarProjection (cfc gapCutoff a) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc gapCutoff a * cfc gapCutoff a = cfc gapCutoff a
  rw [← cfc_mul gapCutoff gapCutoff a gapCutoff_continuous.continuousOn
    gapCutoff_continuous.continuousOn]
  apply cfc_congr
  intro t ht
  rcases hgap t ht with h | h
  · simp [gapCutoff_eq_zero h]
  · simp [gapCutoff_eq_one h]

lemma complexSpectrum_finite {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) : (spectrum ℂ a).Finite := by
  rw [← ha.spectrumRestricts.algebraMap_image]
  exact hfinite.image _

lemma finite_spectrum_cfc {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℂ a).Finite) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a)) :
    (spectrum ℂ (cfc f a)).Finite := by
  apply complexSpectrum_finite (cfc_predicate _ _)
  rw [cfc_map_spectrum f a ha hf]
  exact (realSpectrum_finite ha hfinite).image f

lemma spectrum_shift_lower {a : D} {R t : ℝ} (hR : ‖a‖ + 2 < R)
    (ht : t ∈ spectrum ℝ (a + R • (1 : D))) : 2 < t := by
  cases subsingleton_or_nontrivial D with
  | inl hsubsingleton =>
    let := hsubsingleton
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at ht
  | inr hnontrivial =>
    let := hnontrivial
    have hmem : t - R ∈ spectrum ℝ a := by
      apply (spectrum.add_mem_add_iff (r := t - R) (s := R)).mp
      simpa [Algebra.algebraMap_eq_smul_one, add_comm] using ht
    have hn := spectrum.norm_le_norm_of_mem hmem
    rw [Real.norm_eq_abs] at hn
    have := (abs_le.mp hn).1
    linarith

lemma cutoff_shift_corner {p : D} (hp : IsStarProjection p)
    {a : ProjectionCorner hp} (ha : IsSelfAdjoint a) {R : ℝ} (hR : ‖a‖ + 2 < R) :
    cfc gapCutoff ((a : D) + R • p) = p := by
  let b : ProjectionCorner hp := a + R • 1
  have hb : IsSelfAdjoint b := ha.add ((isSelfAdjoint_iff.mpr (star_trivial R)).smul (IsSelfAdjoint.one _))
  have hbval : (b : D) = (a : D) + R • p := rfl
  rw [← hbval, ← ProjectionCorner.coe_cfc hp hb gapCutoff gapCutoff_continuous gapCutoff_zero]
  have he : cfc gapCutoff b = (1 : ProjectionCorner hp) := by
    rw [← cfc_one ℝ b hb]
    apply cfc_congr
    intro t ht
    exact gapCutoff_eq_one (spectrum_shift_lower hR ht).le
  rw [he, ProjectionCorner.coe_one]

lemma cutoff_shift_corner_gap {p : D} (hp : IsStarProjection p)
    (a : ProjectionCorner hp) {R : ℝ} (hR : ‖a‖ + 2 < R) :
    spectrum ℝ ((a : D) + R • p) ⊆ {t : ℝ | t < 1 ∨ 2 < t} := by
  intro t ht
  have ht' := ProjectionCorner.spectrum_coe_subset hp (a + R • 1) ht
  rcases ht' with ht' | ht'
  · exact Or.inr (spectrum_shift_lower hR ht')
  · exact Or.inl (by simpa only [Set.mem_singleton_iff.mp ht'] using (show (0 : ℝ) < 1 by norm_num))

lemma realRankZero_dense (hD : RealRankZero D) :
    Dense {a : selfAdjoint D | (spectrum ℂ (a : D)).Finite} := by
  intro a
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨b, hb, hbf, hab⟩ := hD a a.property ε hε
  refine ⟨⟨b, hb⟩, hbf, ?_⟩
  rw [dist_eq_norm]
  change ‖(a : D) - b‖ < ε
  exact hab

lemma spectrum_conjugate_unitary {u a : D} (hu : u ∈ unitary D) :
    spectrum ℂ (u * a * star u) = spectrum ℂ a :=
  spectrum.units_conjugate (u := Unitary.toUnits ⟨u, hu⟩)

lemma projection_conjugate_compress {u p q a : D}
    (hq : IsStarProjection q) (hqa : Commute q a)
    (hpu : p * u = u * q) (hup : star u * p = q * star u) :
    p * (u * a * star u) * p = u * (a * q) * star u := by
  calc
    p * (u * a * star u) * p = (p * u) * a * (star u * p) := by simp only [mul_assoc]
    _ = (u * q) * a * (q * star u) := by rw [hpu, hup]
    _ = u * (a * q) * star u := by
      rw [mul_assoc u q a, hqa.eq]
      simp only [mul_assoc, ← mul_assoc q q, hq.isIdempotentElem.eq]

lemma finite_spectrum_cut {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℂ a).Finite) :
    (spectrum ℂ (a * cfc gapCutoff a)).Finite := by
  have he : a * cfc gapCutoff a = cfc (fun t : ℝ => t * gapCutoff t) a := by
    rw [cfc_mul (fun t : ℝ => t) gapCutoff a continuous_id.continuousOn gapCutoff_continuous.continuousOn,
      cfc_id' ℝ a ha]
  rw [he]
  exact finite_spectrum_cfc ha hf _ (continuous_id.mul gapCutoff_continuous).continuousOn

lemma realRankZero_corner (hD : RealRankZero D) {p : D} (hp : IsStarProjection p) :
    RealRankZero (ProjectionCorner hp) := by
  let := CStarAlgebra.spectralOrder D
  let := CStarAlgebra.spectralOrderedRing D
  intro h hh ε hε
  let R : ℝ := ‖h‖ + 3
  have hR : ‖h‖ + 2 < R := by dsimp [R]; linarith
  let b : selfAdjoint D := ⟨(h : D) + R • p,
    (ProjectionCorner.isSelfAdjoint_coe hp hh).add ((isSelfAdjoint_iff.mpr (star_trivial R)).smul hp.isSelfAdjoint)⟩
  let q : selfAdjoint D → D := fun a => cfc gapCutoff (a : D)
  let z : selfAdjoint D → D := fun a => projectionIntertwiner p (q a)
  let u : selfAdjoint D → D := fun a => unitaryPolar (z a)
  let F : selfAdjoint D → D := fun a => p * (u a * (a : D) * star (u a)) * p
  have hqb : q b = p := cutoff_shift_corner hp hh hR
  have hzb : z b = 1 := by dsimp [z]; rw [hqb, projectionIntertwiner_self hp]
  have hub : u b = 1 := by dsimp [u]; rw [hzb, unitaryPolar_one]
  have hFb : F b = (b : D) := by
    dsimp [F]
    rw [hub, star_one, one_mul, mul_one]
    change p * ((h : D) + R • p) * p = (h : D) + R • p
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      h.property.1, h.property.2, hp.isIdempotentElem.eq]
  have hqcont : Continuous q :=
    Continuous.cfc_of_mem_nhdsSet gapCutoff Filter.univ_mem continuous_subtype_val
      (fun a => a.property) gapCutoff_continuous.continuousOn
  have hzcont : Continuous z := by
    dsimp [z, projectionIntertwiner]
    fun_prop
  have hucont : ContinuousAt u b := by
    apply ContinuousAt.comp (f := z) (g := unitaryPolar)
    · rw [hzb]
      exact continuousAt_unitaryPolar_one
    · exact hzcont.continuousAt
  have hFcont : ContinuousAt F b := by
    exact (continuousAt_const.mul ((hucont.mul continuous_subtype_val.continuousAt).mul
      hucont.star)).mul continuousAt_const
  have hnear : ∀ᶠ a in nhds b, ‖F a - (b : D)‖ < ε := by
    simpa only [hFb, dist_eq_norm] using Metric.tendsto_nhds.mp hFcont ε hε
  have hunit : ∀ᶠ a : selfAdjoint D in nhds b, IsUnit (z a) := by
    change z ⁻¹' {x : D | IsUnit x} ∈ nhds b
    apply hzcont.continuousAt.preimage_mem_nhds
    rw [hzb]
    exact Units.nhds (1 : Dˣ)
  let S : Set ℝ := {t | t < 1 ∨ 2 < t}
  have hS : IsOpen S := isOpen_lt continuous_id continuous_const |>.union
    (isOpen_lt continuous_const continuous_id)
  have hgap : ∀ᶠ a : selfAdjoint D in nhds b, ∀ t ∈ spectrum ℝ (a : D), t ≤ 1 ∨ 2 ≤ t := by
    have hbS : S ∈ nhdsSet (spectrum ℝ (b : D)) :=
      hS.mem_nhdsSet.mpr (cutoff_shift_corner_gap hp h hR)
    have he := (upperHemicontinuous_spectrum ℝ D).upperHemicontinuousAt (b : D) S hbS
    have he' := continuous_subtype_val.continuousAt.tendsto.eventually he
    filter_upwards [he'] with a ha
    intro t ht
    exact (subset_of_mem_nhdsSet ha ht).imp le_of_lt le_of_lt
  obtain ⟨a, hfinite, hgap, hunit, hnear⟩ :=
    (realRankZero_dense hD).inter_nhds_nonempty (hgap.and (hunit.and hnear))
  have hqa : IsStarProjection (q a) := spectralCut_isProjection hgap
  have hpu : p * u a = u a * q a := (unitaryPolar_intertwines hp hqa hunit).symm
  have hup : star (u a) * p = q a * star (u a) := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hqa.isSelfAdjoint.star_eq] using
      congrArg star hpu
  have hcomm : Commute (q a) (a : D) := a.property.commute_cfc (Commute.refl _) gapCutoff
  have hFeq : F a = u a * ((a : D) * q a) * star (u a) :=
    projection_conjugate_compress hqa hcomm hpu hup
  let c : ProjectionCorner hp := ProjectionCorner.compress hp (u a * (a : D) * star (u a))
  have hc : IsSelfAdjoint c := by
    apply Subtype.ext
    change star (p * (u a * (a : D) * star (u a)) * p) =
      p * (u a * (a : D) * star (u a)) * p
    simpa only [hp.isSelfAdjoint.star_eq] using
      (a.property.conjugate (u a) |>.conjugate p).star_eq
  have hcf : (spectrum ℂ c).Finite := by
    apply ProjectionCorner.finite_spectrum_of_coe hp
    change (spectrum ℂ (F a)).Finite
    rw [hFeq, spectrum_conjugate_unitary (unitaryPolar_mem hunit)]
    exact finite_spectrum_cut a.property hfinite
  refine ⟨c - R • 1, hc.sub ((isSelfAdjoint_iff.mpr (star_trivial R)).smul (IsSelfAdjoint.one _)), ?_, ?_⟩
  · apply complexSpectrum_finite (hc.sub ((isSelfAdjoint_iff.mpr (star_trivial R)).smul (IsSelfAdjoint.one _)))
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
    exact (realSpectrum_finite hc hcf).sub (Set.finite_singleton R)
  · have he : ((h - (c - R • 1) : ProjectionCorner hp) : D) = (b : D) - F a := by
      change (h : D) - (F a - R • p) = (h : D) + R • p - F a
      abel
    change ‖((h - (c - R • 1) : ProjectionCorner hp) : D)‖ < ε
    rw [he, norm_sub_rev]
    exact hnear

end SpectralCutoffs

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ScalarCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ScalarCompression

variable {D : Type uD} [CStarAlgebra D]

attribute [instance] ProjectionPartition.indexFintype

namespace ProjectionPartition

variable {r : D} (P : ProjectionPartition r)

lemma piece_le [PartialOrder D] [StarOrderedRing D] (hr : IsStarProjection r)
    (i : P.Index) : P.piece i ≤ r :=
  ((P.isProjection i).le_iff_mul_eq_left hr).mpr (P.mul_parent i)

end ProjectionPartition

lemma norm_compress_le {q : D} (hq : IsStarProjection q) (a : D) :
    ‖q * a * q‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖q‖ * ‖a‖ * ‖q‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a‖ * 1 := by
      gcongr <;> exact IsStarProjection.norm_le q hq
    _ = _ := by ring

lemma compression_persist {q r : D} (hq : IsStarProjection q)
    (hqr : q * r = q) (hrq : r * q = q) (a : D) (α : ℂ) :
    ‖q * a * q - α • q‖ ≤ ‖r * a * r - α • r‖ := by
  have he : q * (r * a * r - α • r) * q = q * a * q - α • q := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    simp only [← mul_assoc, hqr, hq.isIdempotentElem.eq]
    rw [mul_assoc (q * a), hrq]
  rw [← he]
  exact norm_compress_le hq _

lemma scalarCompression_selfAdjoint (hD : RealRankZero D) {r : D}
    (hr : IsStarProjection r) (a : D) (ha : IsSelfAdjoint a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ProjectionPartition r, ∀ i, ∃ α : ℂ,
      ‖P.piece i * a * P.piece i - α • P.piece i‖ < ε := by
  let c := ProjectionCorner.compress hr a
  have hc : IsSelfAdjoint c := by
    apply Subtype.ext
    change star (r * a * r) = r * a * r
    simpa only [hr.isSelfAdjoint.star_eq] using (ha.conjugate r).star_eq
  obtain ⟨b, hb, hbf, hcb⟩ := realRankZero_corner hD hr c hc ε hε
  let hf := realSpectrum_finite hb hbf
  let P := cornerSpectralPartition hr hb hf
  refine ⟨P, ?_⟩
  intro i
  let t : hf.toFinset := i
  refine ⟨((t : ℝ) : ℂ), ?_⟩
  have hie : (b : D) * P.piece i = (t : ℝ) • P.piece i :=
    congrArg Subtype.val (spectralAtom_eigenvalue hb hf (t : ℝ))
  have he : P.piece i * ((c : D) - (b : D)) * P.piece i =
      P.piece i * a * P.piece i - ((t : ℝ) : ℂ) • P.piece i := by
    rw [mul_sub, sub_mul]
    change P.piece i * (r * a * r) * P.piece i -
      P.piece i * (b : D) * P.piece i = _
    simp only [← mul_assoc, P.mul_parent i]
    rw [mul_assoc (P.piece i * a), P.parent_mul i,
      mul_assoc (P.piece i) (b : D), hie, mul_smul_comm,
      (P.isProjection i).isIdempotentElem.eq]
    simp only [Complex.coe_smul]
  rw [← he]
  exact (norm_compress_le (P.isProjection i) _).trans_lt hcb

lemma scalarCompressions_selfAdjoint (hD : RealRankZero D) {r : D}
    (hr : IsStarProjection r) (F : Finset (selfAdjoint D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ProjectionPartition r, ∀ a ∈ F, ∀ i, ∃ α : ℂ,
      ‖P.piece i * (a : D) * P.piece i - α • P.piece i‖ < ε := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    by_cases hr0 : r = 0
    · subst r
      exact ⟨ProjectionPartition.empty, by simp⟩
    · exact ⟨ProjectionPartition.singleton hr hr0, by simp⟩
  | @insert a F _ ih =>
    obtain ⟨P, hP⟩ := ih
    have hQ := fun i : P.Index =>
      scalarCompression_selfAdjoint hD (P.isProjection i) (a : D) a.property hε
    choose Q hQ using hQ
    refine ⟨P.refine Q, ?_⟩
    intro b hb i
    change (Σ j : P.Index, (Q j).Index) at i
    rcases i with ⟨i, j⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hQ i j
    · obtain ⟨α, hα⟩ := hP b hb i
      refine ⟨α, ?_⟩
      exact (compression_persist ((Q i).isProjection j) ((Q i).mul_parent j)
        ((Q i).parent_mul j) (b : D) α).trans_lt hα

lemma scalar_compressions (hD : RealRankZero D) {r : D} (hr : IsStarProjection r)
    (F : Finset D) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ProjectionPartition r, ∀ a ∈ F, ∀ i, ∃ α : ℂ,
      ‖P.piece i * a * P.piece i - α • P.piece i‖ < ε := by
  classical
  let S := F.image realPart ∪ F.image imaginaryPart
  obtain ⟨P, hP⟩ := scalarCompressions_selfAdjoint hD hr S (half_pos hε)
  refine ⟨P, ?_⟩
  intro a ha i
  obtain ⟨α, hα⟩ := hP (realPart a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)) i
  obtain ⟨β, hβ⟩ := hP (imaginaryPart a)
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)) i
  refine ⟨α + Complex.I * β, ?_⟩
  have he : P.piece i * a * P.piece i - (α + Complex.I * β) • P.piece i =
      (P.piece i * (realPart a : D) * P.piece i - α • P.piece i) +
      Complex.I • (P.piece i * (imaginaryPart a : D) * P.piece i - β • P.piece i) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, add_smul,
      smul_sub, smul_smul]
    abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_smul, Complex.norm_I, one_mul]
  linarith

end ScalarCompression

section ProjectionOrder

variable {D : Type uD} [CStarAlgebra D]

namespace ProjectionCorner

variable {p : D} (hp : IsStarProjection p)

variable [PartialOrder D] [StarOrderedRing D]

instance instStarOrderedRingSubtypeMemNonUnitalStarSubalgebraComplex : StarOrderedRing (ProjectionCorner hp) := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z : D) + (x : D) ≤ (z : D) + (y : D)
    simpa only [add_comm] using add_le_add_left
      (show (x : D) ≤ (y : D) from h) (z : D)
  · intro a
    constructor
    · intro ha
      have hsa : IsSelfAdjoint a :=
        Subtype.ext (IsSelfAdjoint.of_nonneg (show 0 ≤ (a : D) from ha)).star_eq
      have hspec : ∀ t ∈ spectrum ℝ a, 0 ≤ t := by
        intro t ht
        have hc : (t : ℂ) ∈ spectrum ℂ (a : D) :=
          spectrum_subset_coe hp a (hsa.coe_mem_spectrum_complex.mpr ht)
        exact spectrum_nonneg_of_nonneg (show 0 ≤ (a : D) from ha)
          ((isSelfAdjoint_coe hp hsa).coe_mem_spectrum_complex.mp hc)
      refine ⟨cfc Real.sqrt a, ?_⟩
      rw [(cfc_predicate Real.sqrt a).star_eq,
        ← cfc_mul Real.sqrt Real.sqrt a Real.continuous_sqrt.continuousOn
          Real.continuous_sqrt.continuousOn]
      nth_rw 1 [← cfc_id ℝ a hsa]
      exact cfc_congr (fun t ht => (Real.mul_self_sqrt (hspec t ht)).symm)
    · rintro ⟨s, rfl⟩
      exact star_mul_self_nonneg (s : D)

end ProjectionCorner

end ProjectionOrder

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ColumnSplitting

variable {D : Type uD} [CStarAlgebra D]

lemma partialIsometry_right_support {v e : D} (he : IsStarProjection e)
    (hv : star v * v = e) : v * e = v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  calc
    star (v * e - v) * (v * e - v) =
        e * (star v * v) * e - e * (star v * v) - (star v * v) * e + star v * v := by
      rw [star_sub, star_mul, he.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = 0 := by simp only [hv, he.isIdempotentElem.eq, sub_self, zero_sub, neg_add_cancel]

end ColumnSplitting

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ProportionalProjections

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma orthogonal_projection_sum {I : Type uI} (S : Finset I) (p : I → D)
    (hp : ∀ i ∈ S, IsStarProjection (p i))
    (hortho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsStarProjection.zero D
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    apply (hp a (Finset.mem_insert_self a S)).add
    · exact ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hortho i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact hortho a (Finset.mem_insert_self a S) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))

lemma trace_projection_le_one (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    (τ.functional p).re ≤ 1 := by
  have h := (Complex.le_def.mp (τ.functional.monotone hp.le_one)).1
  change (τ.functional p).re ≤ (τ.functional 1).re at h
  simpa only [τ.normalized, Complex.one_re] using h

end ProportionalProjections

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FiniteLinearTests

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_norm_projection_mul_le (τ : TracialState D) {e : D}
    (he : IsStarProjection e) (b : D) :
    ‖τ.functional (e * b)‖ ≤ ‖b‖ * (τ.functional e).re := by
  rw [← trace_projection_corner τ he b]
  calc
    _ ≤ traceTwoNorm τ (e * b) * traceTwoNorm τ e := trace_norm_mul_le τ _ _
    _ ≤ (‖b‖ * traceTwoNorm τ e) * traceTwoNorm τ e :=
      mul_le_mul_of_nonneg_right (traceTwoNorm_mul_right τ b e) (traceTwoNorm_nonneg τ e)
    _ = ‖b‖ * (τ.functional e).re := by
      rw [← traceTwoNorm_projection_sq τ he]; ring

end FiniteLinearTests

section MatrixRows

variable {D : Type uD} [CStarAlgebra D]

namespace ProjectionRow

variable {I : Type uI} [Fintype I] {q : D} (U : ProjectionRow I q)

lemma right_support (i : I) : U.entry i * q = U.entry i :=
  partialIsometry_right_support U.projection (U.gram_diag i)

lemma coeff_star (a : D) (i j : I) : star (U.coeff a i j) = U.coeff (star a) j i := by
  simp only [coeff, star_mul, star_star, mul_assoc]

lemma coeff_mul [DecidableEq I] (a b : D) (hb : q * b = b) (i j k l : I) :
    U.coeff a i j * U.coeff b k l =
      if j = k then U.coeff (a * b) i l else 0 := by
  classical
  rw [show U.coeff a i j * U.coeff b k l =
    (U.entry i * a) * (star (U.entry j) * U.entry k) * (b * star (U.entry l)) by
      dsimp [coeff]; noncomm_ring]
  by_cases h : j = k
  · subst k
    rw [ite_eq_left rfl, U.gram_diag]
    simp only [coeff, mul_assoc]
    rw [← mul_assoc q b, hb]
  · rw [ite_eq_right h, U.gram_offdiag j k h, mul_zero, zero_mul]

end ProjectionRow

end MatrixRows

section SamplingEstimates

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_supported_norm_le (τ : TracialState D) {p a : D}
    (hp : IsStarProjection p) (hpa : p * a = a) :
    ‖τ.functional a‖ ≤ ‖a‖ * (τ.functional p).re := by
  simpa only [hpa] using trace_norm_projection_mul_le τ hp a

end SamplingEstimates

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

lemma scalar_inv_sqrt_near_one {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
    |t ^ (-(1 / 2) : ℝ) - 1| ≤ 2 * |t - 1| := by
  have ht0 : 0 ≤ t := by linarith
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt t :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : 0 < Real.sqrt t := by linarith
  have hsq := Real.sq_sqrt ht0
  have hfactor : t - 1 = (Real.sqrt t - 1) * (Real.sqrt t + 1) := by nlinarith
  have hsbound : |Real.sqrt t - 1| ≤ |t - 1| := by
    rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt t + 1)]
    nlinarith [abs_nonneg (Real.sqrt t - 1), Real.sqrt_nonneg t]
  rw [Real.rpow_neg ht0, ← Real.sqrt_eq_rpow]
  have hinv : (Real.sqrt t)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hs0).mpr (by nlinarith)
  calc
    |(Real.sqrt t)⁻¹ - 1| = |Real.sqrt t - 1| * (Real.sqrt t)⁻¹ := by
      have he : (Real.sqrt t)⁻¹ - 1 = -(Real.sqrt t - 1) * (Real.sqrt t)⁻¹ := by
        field_simp
        ring
      rw [he, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hs0)]
    _ ≤ |t - 1| * 2 := mul_le_mul hsbound hinv (by positivity) (abs_nonneg _)
    _ = _ := mul_comm _ _

section

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma selfAdjoint_spectrum_near_one {a : D} (ha : IsSelfAdjoint a)
    {δ : ℝ} (hδ : ‖a - 1‖ ≤ δ) {t : ℝ} (ht : t ∈ spectrum ℝ a) :
    |t - 1| ≤ δ := by
  have hf : ContinuousOn (fun x : ℝ => x - 1) (spectrum ℝ a) := by fun_prop
  have h := norm_apply_le_norm_cfc (fun x : ℝ => x - 1) a ht hf ha
  rw [cfc_sub _ _ a, cfc_id' ℝ a ha] at h
  change ‖t - 1‖ ≤ ‖a - cfc (1 : ℝ → ℝ) a‖ at h
  rw [cfc_one ℝ a ha] at h
  exact h.trans hδ

lemma inv_sqrt_near_one {a : D} (ha : 0 ≤ a)
    {δ : ℝ} (hδ : ‖a - 1‖ ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    IsStrictlyPositive a ∧ ‖CFC.rpow a (-(1 / 2) : ℝ) - 1‖ ≤ 2 * δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hs (t : ℝ) (ht : t ∈ spectrum ℝ a) : 1 / 2 ≤ t := by
    have h := selfAdjoint_spectrum_near_one hsa hδ ht
    have := (abs_le.mp h).1
    linarith
  have hsp : IsStrictlyPositive a :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hsa, fun t ht => lt_of_lt_of_le (by norm_num) (hs t ht)⟩
  have hf : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (spectrum ℝ a) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    left
    change t ≠ 0
    linarith [hs t ht]
  refine ⟨hsp, ?_⟩
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha, ← cfc_one ℝ a hsa]
  change ‖cfc (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) a - cfc (fun _ : ℝ => 1) a‖ ≤ 2 * δ
  rw [← cfc_sub _ _ a hf continuousOn_const]
  apply norm_cfc_le (by positivity)
  intro t ht
  exact (scalar_inv_sqrt_near_one (hs t ht)).trans
    (mul_le_mul_of_nonneg_left (selfAdjoint_spectrum_near_one hsa hδ ht) (by norm_num))

end

section SpectralEnergy

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I]

lemma traceTwoNorm_sq_real_smul (τ : TracialState D) (c : ℝ) (a : D) :
    traceTwoNorm τ (c • a) ^ 2 = c ^ 2 * traceTwoNorm τ a ^ 2 := by
  simp only [traceTwoNorm_sq, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    τ.functional.map_smul_of_tower, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma traceTwoNorm_sq_partition_left (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (a : D) :
    ∑ i, traceTwoNorm τ (e i * a) ^ 2 = traceTwoNorm τ a ^ 2 := by
  simp only [traceTwoNorm_sq, star_mul, fun i => (he i).isSelfAdjoint.star_eq]
  simp only [mul_assoc, ← mul_assoc (e _) (e _) a, fun i => (he i).isIdempotentElem.eq]
  rw [← Complex.re_sum, ← map_sum, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]

lemma traceTwoNorm_sq_partition_right (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (a : D) :
    ∑ i, traceTwoNorm τ (a * e i) ^ 2 = traceTwoNorm τ a ^ 2 := by
  calc
    _ = ∑ i, traceTwoNorm τ (e i * star a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← traceTwoNorm_star τ (a * e i), star_mul, (he i).isSelfAdjoint.star_eq]
    _ = traceTwoNorm τ (star a) ^ 2 := traceTwoNorm_sq_partition_left τ e he hs (star a)
    _ = _ := by rw [traceTwoNorm_star]

lemma traceTwoNorm_sq_partition (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (a : D) :
    ∑ i, ∑ j, traceTwoNorm τ (e i * a * e j) ^ 2 = traceTwoNorm τ a ^ 2 := by
  simp only [traceTwoNorm_sq_partition_right τ e he hs]
  exact traceTwoNorm_sq_partition_left τ e he hs a

lemma spectral_commutator_energy (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (a : D) (c : I → ℝ) (hl : ∀ i, e i * a = c i • e i)
    (hr : ∀ i, a * e i = c i • e i) (x : D) :
    traceTwoNorm τ (x * a - a * x) ^ 2 =
      ∑ i, ∑ j, (c i - c j) ^ 2 * traceTwoNorm τ (e i * x * e j) ^ 2 := by
  rw [← traceTwoNorm_sq_partition τ e he hs (x * a - a * x)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : e i * (x * a - a * x) * e j = (c j - c i) • (e i * x * e j) := by
    calc
      _ = e i * x * (a * e j) - (e i * a) * x * e j := by noncomm_ring
      _ = _ := by rw [hr j, hl i]; simp only [mul_smul_comm, smul_mul_assoc, sub_smul]
  rw [h, traceTwoNorm_sq_real_smul, sub_sq_comm]

lemma traceTwoNorm_sq_unitary_mul (τ : TracialState D) (x : unitary D) (a : D) :
    traceTwoNorm τ ((x : D) * a) ^ 2 = traceTwoNorm τ a ^ 2 := by
  rw [traceTwoNorm_sq, traceTwoNorm_sq, star_mul]
  simp only [mul_assoc, ← mul_assoc (star (x : D)) (x : D), x.property.1, one_mul]

lemma traceTwoNorm_sq_mul_unitary (τ : TracialState D) (x : unitary D) (a : D) :
    traceTwoNorm τ (a * (x : D)) ^ 2 = traceTwoNorm τ a ^ 2 := by
  rw [← traceTwoNorm_star τ (a * (x : D)), star_mul]
  change traceTwoNorm τ (((star x : unitary D) : D) * star a) ^ 2 = _
  rw [traceTwoNorm_sq_unitary_mul, traceTwoNorm_star]

lemma traceTwoNorm_sq_projection (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    traceTwoNorm τ p ^ 2 = (τ.functional p).re := by
  rw [traceTwoNorm_sq, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

end SpectralEnergy

section SpectralRoot

variable {D : Type uD} [CStarAlgebra D]

variable {I : Type uI} [Fintype I]

lemma projection_combination_mul (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (c : I → ℝ) (j : I) :
    (∑ i, c i • e i) * e j = c j • e j := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · rw [smul_mul_assoc, (he j).isIdempotentElem.eq]
  · intro i _ hij
    rw [smul_mul_assoc, ho hij, smul_zero]
  · simp

lemma projection_mul_combination (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (c : I → ℝ) (j : I) :
    e j * (∑ i, c i • e i) = c j • e j := by
  simpa only [star_mul, star_sum, star_smul, star_trivial,
    fun i => (he i).isSelfAdjoint.star_eq] using
      congrArg star (projection_combination_mul e he ho c j)

variable [PartialOrder D] [StarOrderedRing D]

lemma projection_combination_nonneg (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) : 0 ≤ ∑ i, c i • e i :=
  Finset.sum_nonneg (fun i _ => smul_nonneg (hc i) (he i).nonneg)

lemma sqrt_projection_combination (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    CFC.sqrt (∑ i, c i • e i) = ∑ i, Real.sqrt (c i) • e i := by
  apply (CFC.sqrt_eq_iff _ _ (projection_combination_nonneg e he c hc)
    (projection_combination_nonneg e he _ (fun i => Real.sqrt_nonneg _))).mpr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, projection_combination_mul e he ho, smul_smul,
    ← sq, Real.sq_sqrt (hc j)]

end SpectralRoot

lemma weighted_spectral_cauchy {I : Type uI} [Fintype I]
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (w : I → I → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∑ i, ∑ j, |c i - c j| * w i j) ^ 2 ≤
      (∑ i, ∑ j, (Real.sqrt (c i) - Real.sqrt (c j)) ^ 2 * w i j) *
      (∑ i, ∑ j, (Real.sqrt (c i) + Real.sqrt (c j)) ^ 2 * w i j) := by
  classical
  simp only [← Fintype.sum_prod_type']
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact mul_nonneg (sq_nonneg _) (hw i.1 i.2)
  · intro i _; exact mul_nonneg (sq_nonneg _) (hw i.1 i.2)
  · intro i _
    rw [mul_pow, sq_abs]
    have he : c i.1 - c i.2 =
        (Real.sqrt (c i.1) - Real.sqrt (c i.2)) *
          (Real.sqrt (c i.1) + Real.sqrt (c i.2)) := by
      nlinarith [Real.sq_sqrt (hc i.1), Real.sq_sqrt (hc i.2)]
    rw [he]
    ring_nf
    exact le_rfl

section SpectralEstimate

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I]

lemma traceTwoNorm_sq_partition_unitary_row (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (x : unitary D) (i : I) :
    ∑ j, traceTwoNorm τ (e i * (x : D) * e j) ^ 2 = (τ.functional (e i)).re := by
  rw [traceTwoNorm_sq_partition_right τ e he hs, traceTwoNorm_sq_mul_unitary,
    traceTwoNorm_sq_projection τ (he i)]

lemma traceTwoNorm_sq_partition_unitary_col (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (x : unitary D) (j : I) :
    ∑ i, traceTwoNorm τ (e i * (x : D) * e j) ^ 2 = (τ.functional (e j)).re := by
  simp only [mul_assoc]
  rw [traceTwoNorm_sq_partition_left τ e he hs, traceTwoNorm_sq_unitary_mul,
    traceTwoNorm_sq_projection τ (he j)]

omit [StarOrderedRing D] in
lemma trace_projection_combination (τ : TracialState D) (e : I → D) (c : I → ℝ) :
    (τ.functional (∑ i, c i • e i)).re = ∑ i, c i * (τ.functional (e i)).re := by
  simp only [map_sum, τ.functional.map_smul_of_tower, Complex.re_sum,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma spectral_root_sum_le (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (x : unitary D) :
    (∑ i, ∑ j, (Real.sqrt (c i) + Real.sqrt (c j)) ^ 2 *
      traceTwoNorm τ (e i * (x : D) * e j) ^ 2) ≤
        4 * (τ.functional (∑ i, c i • e i)).re := by
  calc
    _ ≤ ∑ i, ∑ j, (2 * c i + 2 * c j) *
        traceTwoNorm τ (e i * (x : D) * e j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [Real.sq_sqrt (hc i), Real.sq_sqrt (hc j),
        sq_nonneg (Real.sqrt (c i) - Real.sqrt (c j))]
    _ = 4 * (τ.functional (∑ i, c i • e i)).re := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => 2 * c j *
        traceTwoNorm τ (e i * (x : D) * e j) ^ 2)]
      simp only [← Finset.mul_sum, traceTwoNorm_sq_partition_unitary_row τ e he hs,
        traceTwoNorm_sq_partition_unitary_col τ e he hs]
      rw [trace_projection_combination]
      simp only [mul_assoc, ← Finset.mul_sum]
      ring

lemma sqrt_unitary_conjugate {b : D} (hb : 0 ≤ b) (x : unitary D) :
    CFC.sqrt ((x : D) * b * star (x : D)) =
      (x : D) * CFC.sqrt b * star (x : D) := by
  apply CFC.sqrt_unique (hb := star_right_conjugate_nonneg (CFC.sqrt_nonneg b) _)
  calc
    _ = (x : D) * (CFC.sqrt b * CFC.sqrt b) * star (x : D) := by
      simp only [mul_assoc, ← mul_assoc (star (x : D)) (x : D), x.property.1, one_mul]
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self b hb]

lemma root_commutator_sq_le (τ : TracialState D) {b : D} (hb : 0 ≤ b) (x : unitary D) :
    traceTwoNorm τ ((x : D) * CFC.sqrt b - CFC.sqrt b * (x : D)) ^ 2 ≤
      traceOneNorm τ (b - (x : D) * b * star (x : D)) := by
  have hpos : 0 ≤ (x : D) * b * star (x : D) := star_right_conjugate_nonneg hb _
  have h := powers_stormer τ hb hpos
  rw [sqrt_unitary_conjugate hb x] at h
  calc
    _ = traceTwoNorm τ ((CFC.sqrt b - (x : D) * CFC.sqrt b * star (x : D)) *
        (x : D)) ^ 2 := by
      have he : (CFC.sqrt b - (x : D) * CFC.sqrt b * star (x : D)) * (x : D) =
          -((x : D) * CFC.sqrt b - CFC.sqrt b * (x : D)) := by
        simp only [sub_mul, mul_assoc, x.property.1, mul_one, neg_sub]
      rw [he]
      simp only [traceTwoNorm_eq_gns, map_neg, norm_neg]
    _ = _ := traceTwoNorm_sq_mul_unitary τ x _
    _ ≤ _ := h

theorem finite_spectral_energy (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (ho : Pairwise (fun i j => e i * e j = 0))
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (x : unitary D) :
    (∑ i, ∑ j, |c i - c j| * traceTwoNorm τ (e i * (x : D) * e j) ^ 2) ≤
      2 * Real.sqrt ((τ.functional (∑ i, c i • e i)).re *
        traceOneNorm τ ((∑ i, c i • e i) -
          (x : D) * (∑ i, c i • e i) * star (x : D))) := by
  let b := ∑ i, c i • e i
  have hb : 0 ≤ b := projection_combination_nonneg e he c hc
  have hm : 0 ≤ (τ.functional b).re := (τ.functional.map_nonneg hb).1
  have hcs := weighted_spectral_cauchy c hc
    (fun i j => traceTwoNorm τ (e i * (x : D) * e j) ^ 2) (fun i j => sq_nonneg _)
  have hroot : (∑ i, ∑ j, (Real.sqrt (c i) - Real.sqrt (c j)) ^ 2 *
      traceTwoNorm τ (e i * (x : D) * e j) ^ 2) =
      traceTwoNorm τ ((x : D) * CFC.sqrt b - CFC.sqrt b * (x : D)) ^ 2 := by
    dsimp only [b]
    rw [sqrt_projection_combination e he ho c hc]
    exact (spectral_commutator_energy τ e he hs _ _
      (projection_mul_combination e he ho _) (projection_combination_mul e he ho _) _).symm
  rw [hroot] at hcs
  have hsum := spectral_root_sum_le τ e he hs c hc x
  have hsquare := hcs.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  have hpow := root_commutator_sq_le τ hb x
  have hfinal := hsquare.trans (mul_le_mul_of_nonneg_right hpow (mul_nonneg (by norm_num) hm))
  have hnonneg : 0 ≤ (τ.functional b).re * traceOneNorm τ (b - (x : D) * b * star (x : D)) :=
    mul_nonneg hm (traceOneNorm_nonneg τ _)
  have hsqrt := Real.sq_sqrt hnonneg
  have hsqrt0 := Real.sqrt_nonneg ((τ.functional b).re *
    traceOneNorm τ (b - (x : D) * b * star (x : D)))
  change _ ≤ 2 * Real.sqrt ((τ.functional b).re *
    traceOneNorm τ (b - (x : D) * b * star (x : D)))
  nlinarith

end SpectralEstimate

section LayerCake

variable {I : Type uI} [Fintype I] [LinearOrder I]

omit [Fintype I] in
lemma cutCoefficient_nonneg (j i : I) : 0 ≤ cutCoefficient j i := by
  unfold cutCoefficient
  split <;> norm_num

omit [Fintype I] in
lemma cutCoefficient_mono (j : I) : Monotone (cutCoefficient j) := by
  intro i k hik
  unfold cutCoefficient
  split_ifs with hji hjk
  · exact le_rfl
  · exact (hjk (hji.trans hik)).elim
  · norm_num
  · exact le_rfl

lemma layerCoefficient_nonneg (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (i : I) :
    0 ≤ layerCoefficient w i :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (cutCoefficient_nonneg j i))

lemma layerCoefficient_mono (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Monotone (layerCoefficient w) := by
  intro i k hik
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (cutCoefficient_mono j hik) (hw j))

lemma cut_difference_sum_of_le (w : I → ℝ) (i k : I) (hik : i ≤ k) :
    (∑ j, w j * (cutCoefficient j i - cutCoefficient j k) ^ 2) =
      layerCoefficient w k - layerCoefficient w i := by
  rw [layerCoefficient, layerCoefficient, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold cutCoefficient
  split_ifs with hji hjk
  · ring
  · exact (hjk (hji.trans hik)).elim
  · ring
  · ring

lemma cut_difference_sum (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (i k : I) :
    (∑ j, w j * (cutCoefficient j i - cutCoefficient j k) ^ 2) =
      |layerCoefficient w i - layerCoefficient w k| := by
  rcases le_total i k with hik | hki
  · rw [cut_difference_sum_of_le w i k hik,
      abs_of_nonpos (sub_nonpos.mpr (layerCoefficient_mono w hw hik))]
    ring
  · simp only [sub_sq_comm (cutCoefficient _ i) (cutCoefficient _ k)]
    rw [cut_difference_sum_of_le w k i hki,
      abs_of_nonneg (sub_nonneg.mpr (layerCoefficient_mono w hw hki))]

variable {D : Type uD} [CStarAlgebra D]

lemma layer_decomposition (e : I → D) (w : I → ℝ) :
    (∑ j, w j • upperLayerCut e j) = ∑ i, layerCoefficient w i • e i := by
  simp only [upperLayerCut, Finset.smul_sum, smul_smul, layerCoefficient, Finset.sum_smul]
  exact Finset.sum_comm

variable [PartialOrder D] [StarOrderedRing D]

theorem layer_energy (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (ho : Pairwise (fun i j => e i * e j = 0))
    (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (x : D) :
    (∑ j, w j * traceTwoNorm τ (x * upperLayerCut e j - upperLayerCut e j * x) ^ 2) =
    ∑ i, ∑ k, |layerCoefficient w i - layerCoefficient w k| *
      traceTwoNorm τ (e i * x * e k) ^ 2 := by
  simp_rw [upperLayerCut, spectral_commutator_energy τ e he hs _ _
    (projection_mul_combination e he ho _) (projection_combination_mul e he ho _) x]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [← mul_assoc, ← Finset.sum_mul, cut_difference_sum w hw]

theorem layer_energy_le (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (ho : Pairwise (fun i j => e i * e j = 0))
    (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (x : unitary D) :
    (∑ j, w j * traceTwoNorm τ ((x : D) * upperLayerCut e j -
      upperLayerCut e j * (x : D)) ^ 2) ≤
      2 * Real.sqrt ((τ.functional (∑ j, w j • upperLayerCut e j)).re *
        traceOneNorm τ ((∑ j, w j • upperLayerCut e j) -
          (x : D) * (∑ j, w j • upperLayerCut e j) * star (x : D))) := by
  rw [layer_energy τ e he hs ho w hw, layer_decomposition e w]
  exact finite_spectral_energy τ e he hs ho _ (layerCoefficient_nonneg w hw) x

end LayerCake

section LayerWeights

lemma orderedLayerValues_mono {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) : Monotone (Fin.cons (α := fun _ => ℝ) 0 c) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact hc j
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j => exact hm (Fin.succ_le_succ_iff.mp hij)

lemma orderedLayerWeights_nonneg {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) (j : Fin n) :
    0 ≤ orderedLayerWeights c j := by
  dsimp only [orderedLayerWeights]
  apply sub_nonneg.mpr
  exact orderedLayerValues_mono c hc hm (Fin.castSucc_le_succ j)

lemma orderedLayerWeights_le {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (j : Fin n) : orderedLayerWeights c j ≤ c j := by
  have h : 0 ≤ Fin.cons (α := fun _ => ℝ) 0 c j.castSucc := by
    cases he : j.castSucc using Fin.cases with
    | zero => simp
    | succ k => simpa using hc k
  simpa only [orderedLayerWeights, Fin.cons_succ, sub_le_self_iff] using h

lemma layerCoefficient_orderedLayerWeights {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    layerCoefficient (orderedLayerWeights c) i = c i := by
  classical
  have h := Fin.sum_Iic_sub i (Fin.cons (α := fun _ => ℝ) 0 c)
  simp only [Fin.cons_succ, Fin.cons_zero, sub_zero] at h
  convert h using 1
  simp only [layerCoefficient, cutCoefficient, orderedLayerWeights, mul_ite, mul_one,
    mul_zero, ← Finset.sum_filter]
  congr 1
  ext j
  simp

end LayerWeights

section LayerComplete

variable {D : Type uD} [CStarAlgebra D] {n : ℕ}

lemma projection_sum_mul_atom (e : Fin n → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (j : Fin n) :
    (∑ i, e i) * e j = e j := by
  simpa using projection_combination_mul e he ho (fun _ => 1) j

lemma projection_atom_mul_sum (e : Fin n → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (j : Fin n) :
    e j * (∑ i, e i) = e j := by
  simpa using projection_mul_combination e he ho (fun _ => 1) j

lemma completeResolution_projection (e : Fin n → D)
    (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (i : Fin (n + 1)) :
    IsStarProjection (completeResolution e i) := by
  cases i using Fin.cases with
  | zero =>
    exact (orthogonal_projection_sum Finset.univ e (fun i _ => he i)
      (fun i _ j _ hij => ho hij)).one_sub
  | succ i => exact he i

lemma completeResolution_orthogonal (e : Fin n → D)
    (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) :
    Pairwise (fun i j => completeResolution e i * completeResolution e j = 0) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      change (1 - ∑ i, e i) * e j = 0
      rw [sub_mul, one_mul, projection_sum_mul_atom e he ho, sub_self]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      change e i * (1 - ∑ j, e j) = 0
      rw [mul_sub, mul_one, projection_atom_mul_sum e he ho, sub_self]
    | succ j => exact ho (fun h => hij (congrArg Fin.succ h))

lemma completeResolution_sum (e : Fin n → D) : ∑ i, completeResolution e i = 1 := by
  rw [Fin.sum_univ_succ]
  simp [completeResolution]

lemma upperLayerCut_completeResolution_succ (e : Fin n → D) (j : Fin n) :
    upperLayerCut (completeResolution e) j.succ = upperLayerCut e j := by
  simp only [upperLayerCut, Fin.sum_univ_succ, completeResolution, Fin.cons_zero,
    Fin.cons_succ, cutCoefficient, Fin.succ_le_succ_iff]
  simp

variable [PartialOrder D] [StarOrderedRing D]

theorem layer_energy_le_of_orthogonal (τ : TracialState D) (e : Fin n → D)
    (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0))
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (x : unitary D) :
    (∑ j, w j * traceTwoNorm τ ((x : D) * upperLayerCut e j -
      upperLayerCut e j * (x : D)) ^ 2) ≤
      2 * Real.sqrt ((τ.functional (∑ j, w j • upperLayerCut e j)).re *
        traceOneNorm τ ((∑ j, w j • upperLayerCut e j) -
          (x : D) * (∑ j, w j • upperLayerCut e j) * star (x : D))) := by
  have hpos : ∀ j, 0 ≤ Fin.cons (α := fun _ => ℝ) 0 w j := by
    intro j
    cases j using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact hw j
  have h := layer_energy_le τ (completeResolution e) (completeResolution_projection e he ho)
    (completeResolution_sum e) (completeResolution_orthogonal e he ho)
    (Fin.cons (α := fun _ => ℝ) 0 w) hpos x
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_smul,
    zero_add, upperLayerCut_completeResolution_succ] using h

end LayerComplete

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.MatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI uι uκ

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section MatrixTools

variable {ι : Type uι} {κ : Type uκ} {D : Type uD} [Fintype ι] [Fintype κ]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

open CStarMatrix WithCStarModule in

lemma matrix_norm_le_sum (M : CStarMatrix ι κ D) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j

lemma matrix_norm_le_card_mul {M : CStarMatrix ι κ D} {ε : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ ε) :
    ‖M‖ ≤ Fintype.card ι * Fintype.card κ * ε := by
  refine (matrix_norm_le_sum M).trans ?_
  calc
    _ ≤ ∑ _ : κ, ∑ _ : ι, ε := by gcongr with j _ i _; exact h i j
    _ = _ := by simp; ring

end MatrixTools

end CurrentMain

namespace Pureness

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointFunctionalComplex_apply (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointFunctionalComplex f a = (f a : ℂ) := by
  have hr : ℜ (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [selfAdjointFunctionalComplex, hr, a.property.imaginaryPart]

lemma selfAdjointFunctional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hn : ‖f‖ ≤ 1) (h1 : f 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ f a := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖(a : A)‖ := norm_pos_iff.mpr (fun h => hz (Subtype.ext h))
  let b : selfAdjoint A := ‖(a : A)‖⁻¹ • a
  have hb0 : 0 ≤ (b : A) := smul_nonneg (by positivity) ha
  have hbn : ‖(b : A)‖ ≤ 1 := by
    change ‖‖(a : A)‖⁻¹ • (a : A)‖ ≤ 1
    simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hb1 : (b : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn
  have hsub : ‖(1 : selfAdjoint A) - b‖ ≤ 1 := by
    change ‖(1 : A) - (b : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hb1)).mpr
      (sub_le_self _ hb0)
  have hf : ‖f (1 - b)‖ ≤ 1 :=
    (f.le_opNorm _).trans ((mul_le_mul hn hsub (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hfb : 0 ≤ f b := by
    have := le_abs_self (f (1 - b))
    rw [map_sub, h1] at hf this
    change |1 - f b| ≤ 1 at hf
    linarith
  change 0 ≤ f (‖(a : A)‖⁻¹ • a) at hfb
  rw [map_smul, smul_eq_mul] at hfb
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp hfb

theorem exists_normalizedPositiveState [Nontrivial A] :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 := by
  have hn1 : ‖(1 : selfAdjoint A)‖ = 1 := norm_one (α := A)
  obtain ⟨f, hfn, hf1⟩ := exists_dual_vector ℝ (1 : selfAdjoint A) (by rw [hn1]; norm_num)
  have hf1' : f 1 = 1 := by simpa [hn1] using hf1
  let g := selfAdjointFunctionalComplex f.toLinearMap
  have hg : ∀ a : A, 0 ≤ a → 0 ≤ g a := by
    intro a ha
    have h := selfAdjointFunctional_nonneg f hfn.le hf1' ⟨a, .of_nonneg ha⟩ ha
    change 0 ≤ selfAdjointFunctionalComplex f.toLinearMap (⟨a, .of_nonneg ha⟩ : selfAdjoint A)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast h
  refine ⟨{ toLinearMap := g, monotone' := ?_ }, ?_⟩
  · intro a b hab
    change g a ≤ g b
    have := hg (b - a) (sub_nonneg.mpr hab)
    simpa only [map_sub, sub_nonneg] using this
  · change selfAdjointFunctionalComplex f.toLinearMap ((1 : selfAdjoint A) : A) = 1
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast hf1'

end Pureness

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma rowGram_mul (a : I → D) (Z : CStarMatrix I I D) :
    rowGram (rowMul a Z) = star Z * rowGram a * Z := by
  ext i j
  change star (∑ k, a k * Z k i) * (∑ l, a l * Z l j) =
    ∑ l, (∑ k, star (Z k i) * (star (a k) * a l)) * Z l j
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [mul_assoc]

local instance instIsometricContinuousFunctionalCalculusRealCStarMatrixIsSelfAdjoint_solutions_1 : IsometricContinuousFunctionalCalculus ℝ (CStarMatrix I I D)
    IsSelfAdjoint := IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

local instance instNonnegSpectrumClassRealCStarMatrix_solutions_1 : NonnegSpectrumClass ℝ (CStarMatrix I I D) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma selfAdjoint_near_one_strictlyPositive {a : D} (ha : IsSelfAdjoint a)
    {δ : ℝ} (hδ : ‖a - 1‖ ≤ δ) (hδhalf : δ ≤ 1 / 2) : IsStrictlyPositive a := by
  apply CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
  refine ⟨ha, fun t ht => ?_⟩
  have h := (abs_le.mp (selfAdjoint_spectrum_near_one ha hδ ht)).1
  linarith

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma rowMul_norm_sub_le (a : I → D) (Z W : CStarMatrix I I D) {δ : ℝ}
    (h : ∀ i j, ‖Z i j - W i j‖ ≤ δ) (i : I) :
    ‖rowMul a Z i - rowMul a W i‖ ≤ (∑ j, ‖a j‖) * δ := by
  rw [rowMul, rowMul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖a j * Z j i - a j * W j i‖ := norm_sum_le _ _
    _ = ∑ j, ‖a j * (Z j i - W j i)‖ := by simp only [mul_sub]
    _ ≤ ∑ j, ‖a j‖ * δ := Finset.sum_le_sum fun j _ =>
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (h j i) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

theorem normalize_almost_row {q : D} (hq : IsStarProjection q) (a : I → D)
    (ha : ∀ i, a i * q = a i) {ε : ℝ}
    (hg : ∀ i j, ‖star (a i) * a j - (if i = j then q else 0)‖ ≤ ε)
    (hε : (Fintype.card I : ℝ) ^ 2 * ε ≤ 1 / 2) :
    ∃ U : ProjectionRow I q, ∀ i,
      ‖U.entry i - a i‖ ≤ 2 * (∑ j, ‖a j‖) * (Fintype.card I : ℝ) ^ 2 * ε := by
  let F := ProjectionCorner hq
  let X : CStarMatrix I I F := CStarMatrix.ofMatrix fun i j =>
    ⟨star (a i) * a j, by
      have hleft : q * star (a i) = star (a i) := by
        simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star (ha i)
      simp only [← mul_assoc, hleft], by simp only [mul_assoc, ha]⟩
  let ι : CStarMatrix I I F →⋆ₙₐ[ℂ] CStarMatrix I I D :=
    CStarMatrix.mapₙₐ (ProjectionCorner.inclusion hq)
  have hXmap : ι X = rowGram a := rfl
  have hXsa : IsSelfAdjoint X := by
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    change star (star (a j) * a i) = star (a i) * a j
    simp only [star_mul, star_star]
  let δ : ℝ := (Fintype.card I : ℝ) ^ 2 * ε
  have hXnorm : ‖X - 1‖ ≤ δ := by
    have hb (i j : I) : ‖(X - 1) i j‖ ≤ ε := by
      have heq : ((X - 1) i j : D) = star (a i) * a j -
          (if i = j then q else 0) := by
        change star (a i) * a j - ↑((1 : CStarMatrix I I F) i j) = _
        rw [CStarMatrix.one_apply]
        split_ifs <;> rfl
      change ‖((X - 1) i j : D)‖ ≤ ε
      rw [heq]
      exact hg i j
    simpa only [δ, pow_two, mul_assoc] using matrix_norm_le_card_mul hb
  have hXp : IsStrictlyPositive X :=
    selfAdjoint_near_one_strictlyPositive hXsa hXnorm hε
  have hXZ := inv_sqrt_near_one hXp.nonneg hXnorm hε
  let Z : CStarMatrix I I F := CFC.rpow X (-(1 / 2) : ℝ)
  have hZsa : IsSelfAdjoint Z := .of_nonneg CFC.rpow_nonneg
  have hZXZ : star Z * X * Z = 1 := by
    rw [hZsa.star_eq]
    exact CFC.conjugate_rpow_neg_one_half X hXp
  let u := rowMul a (ι Z)
  have hug : rowGram u = ι 1 := by
    rw [rowGram_mul, ← hXmap, ← map_star, ← map_mul, ← map_mul, hZXZ]
  have hu (i j : I) : star (u i) * u j = if i = j then q else 0 := by
    have h := congrArg (fun T : CStarMatrix I I D => T i j) hug
    change star (u i) * u j = ((1 : CStarMatrix I I F) i j : D) at h
    rw [CStarMatrix.one_apply] at h
    split_ifs at h ⊢ <;> exact h
  refine ⟨⟨hq, u, fun i => by simpa using hu i i,
    fun i j hij => by simpa [hij] using hu i j⟩, ?_⟩
  intro i
  change ‖rowMul a (ι Z) i - a i‖ ≤ _
  have hunit : rowMul a (ι 1) = a := by
    ext i
    simp only [rowMul]
    change (∑ j, a j * ((1 : CStarMatrix I I F) j i : D)) = a i
    simp only [CStarMatrix.one_apply, mul_ite, mul_zero,
      apply_ite (fun t : F => (t : D)), ProjectionCorner.coe_one,
      ZeroMemClass.coe_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left, ha]
  have hzentry (i j : I) : ‖ι Z i j - ι 1 i j‖ ≤ 2 * δ := by
    change ‖((Z - 1) i j : D)‖ ≤ 2 * δ
    have h := CStarMatrix.norm_entry_le_norm (M := Z - 1) (i := i) (j := j)
    exact h.trans hXZ.2
  have h := rowMul_norm_sub_le a _ _ hzentry i
  rw [hunit] at h
  convert h using 1
  dsimp [δ]
  ring

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma state_norm_le (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : D) : ‖f a‖ ≤ ‖a‖ := by
  have hone : ‖f.toPreGNS 1‖ = 1 := by
    change Real.sqrt (f (star (1 : D) * 1)).re = 1
    simp [hf]
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  have hgns : ‖f.toPreGNS a‖ ≤ ‖a‖ := by
    calc
      _ = ‖f.leftMulMapPreGNS a (f.toPreGNS 1)‖ := by simp
      _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS 1‖ := (f.leftMulMapPreGNS a).le_opNorm _
      _ ≤ ‖a‖ := by rw [hone, mul_one]; exact hop
  have h := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS 1) (f.toPreGNS a)
  have h' : ‖f a‖ ≤ ‖f.toPreGNS a‖ := by
    simpa only [PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hone, one_mul] using h
  exact h'.trans hgns

namespace ProjectionCorner

variable {q : D} (hq : IsStarProjection q)

lemma compressPositive_one : compressPositive hq 1 = 1 := by
  apply Subtype.ext
  change q * 1 * q = q
  simp only [mul_one, hq.isIdempotentElem.eq]

lemma compressPositive_self : compressPositive hq q = 1 := by
  apply Subtype.ext
  change q * q * q = q
  simp only [hq.isIdempotentElem.eq]

end ProjectionCorner

lemma exists_state_at_projection {q : D} (hq : IsStarProjection q) (hne : q ≠ 0) :
    ∃ f : D →ₚ[ℂ] ℂ, f 1 = 1 ∧ f q = 1 := by
  have : Nontrivial (ProjectionCorner hq) := by
    apply nontrivial_of_ne (1 : ProjectionCorner hq) 0
    intro h
    exact hne (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ := Pureness.exists_normalizedPositiveState (A := ProjectionCorner hq)
  refine ⟨f.comp (ProjectionCorner.compressPositive hq), ?_, ?_⟩
  · change f (ProjectionCorner.compressPositive hq 1) = 1
    rw [ProjectionCorner.compressPositive_one, hf]
  · change f (ProjectionCorner.compressPositive hq q) = 1
    rw [ProjectionCorner.compressPositive_self, hf]

lemma state_scalar_error (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) {q : D}
    (hq : IsStarProjection q) (hfq : f q = 1) (a : D) (c : ℂ) :
    ‖a - f a • q‖ ≤ 2 * ‖a - c • q‖ := by
  have hcoeff : ‖f a - c‖ ≤ ‖a - c • q‖ := by
    simpa only [map_sub, map_smul, hfq, smul_eq_mul, mul_one] using
      state_norm_le f hf (a - c • q)
  calc
    _ = ‖(a - c • q) - ((f a - c) • q)‖ := by congr 1; rw [sub_smul]; abel
    _ ≤ ‖a - c • q‖ + ‖(f a - c) • q‖ := norm_sub_le _ _
    _ ≤ ‖a - c • q‖ + ‖a - c • q‖ := by
      gcongr
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left hq.norm_le (norm_nonneg _)).trans
        (by simpa only [mul_one] using hcoeff)
    _ = _ := by ring

end

open scoped ComplexOrder

section RowRotate

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I] [CStarAlgebra D]

omit [DecidableEq I] in
lemma rowPair_rotate (a : I → D) (Z : Matrix I I ℂ) (x : D) (i j : I) :
    rowPair (rotateRow a Z) x i j =
      ∑ k, ∑ l, (star (Z k i) * Z l j) • rowPair a x k l := by
  simp only [rowPair, rotateRow, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  congr 1; ring

omit [DecidableEq I] in
lemma rotateRow_right_support {q : D} (a : I → D) (ha : ∀ i, a i * q = a i)
    (Z : Matrix I I ℂ) (i : I) : rotateRow a Z i * q = rotateRow a Z i := by
  simp only [rotateRow, Finset.sum_mul, smul_mul_assoc, ha]

lemma rotateRow_norm_le (a : I → D) (Z : Matrix.unitaryGroup I ℂ) (i : I) :
    ‖rotateRow a Z i‖ ≤ ∑ j, ‖a j‖ := by
  calc
    _ ≤ ∑ j, ‖Z j i • a j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖a j‖ := Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (entry_norm_bound_of_unitary Z.property j i)
        (norm_nonneg _)).trans_eq (one_mul _)

lemma rotateRow_covariance (a : I → D) (Z : Matrix.unitaryGroup I ℂ) :
    ∑ i, rotateRow a Z i * star (rotateRow a Z i) = ∑ i, a i * star (a i) := by
  have hZ (k l : I) : ∑ i, Z k i * star (Z l i) = if k = l then 1 else 0 := by
    have h := congrArg (fun M : Matrix I I ℂ => M k l) Z.property.2
    simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply] using h
  calc
    _ = ∑ i, ∑ k, ∑ l, (Z k i * star (Z l i)) • (a k * star (a l)) := by
      simp only [rotateRow, star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
        smul_mul_smul_comm]
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ l, (∑ i, Z k i * star (Z l i)) • (a k * star (a l)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = _ := by
      simp only [hZ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]

lemma rowPair_rotate_error {q : D} (a : I → D) (Z : Matrix.unitaryGroup I ℂ)
    (x : D) (H : Matrix I I ℂ) {δ : ℝ}
    (h : ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ δ) (i j : I) :
    ‖rowPair (rotateRow a Z) x i j - (star (Z : Matrix I I ℂ) * H * Z) i j • q‖ ≤
      (Fintype.card I : ℝ) ^ 2 * δ := by
  have he : (star (Z : Matrix I I ℂ) * H * Z) i j • q =
      ∑ k, ∑ l, (star (Z k i) * Z l j) • (H k l • q) := by
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Finset.sum_mul, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    congr 1; ring
  rw [rowPair_rotate, he, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← smul_sub]
  calc
    _ ≤ ∑ k, ∑ l, ‖(star (Z k i) * Z l j) • (rowPair a x k l - H k l • q)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ _k : I, ∑ _l : I, δ := Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
      rw [norm_smul, norm_mul, norm_star]
      have hcoeff : ‖Z k i‖ * ‖Z l j‖ ≤ 1 :=
        (mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary Z.property k i)).trans
          (entry_norm_bound_of_unitary Z.property l j)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa only [one_mul] using h k l)
    _ = _ := by simp [pow_two]; ring

end RowRotate

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.RowEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma entry_norm_le (i : I) : ‖U.entry i‖ ≤ 1 := by
  have h : ‖U.entry i‖ * ‖U.entry i‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, U.gram_diag]
    exact U.projection.norm_le
  nlinarith [norm_nonneg (U.entry i)]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma range_eq_sum : U.sample q = ∑ i, U.entry i * star (U.entry i) := by
  simp only [sample, coeff, U.right_support]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma compression_expand (x : D) :
    U.sample q * x * U.sample q =
      ∑ i, ∑ j, U.entry i * rowPair U.entry x i j * star (U.entry j) := by
  rw [U.range_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, rowPair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [mul_assoc]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma compression_norm_le (x : D) (H : Matrix I I ℂ) {δ : ℝ}
    (h : ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤ δ) :
    ‖U.sample q * x * U.sample q - U.matrix q H‖ ≤ (Fintype.card I : ℝ) ^ 2 * δ := by
  have hmat : U.matrix q H = ∑ i, ∑ j, U.entry i * (H i j • q) * star (U.entry j) := by
    simp only [matrix, coeff, mul_smul_comm, smul_mul_assoc]
  rw [U.compression_expand, hmat, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ∑ j, ‖U.entry i * rowPair U.entry x i j * star (U.entry j) -
        U.entry i * (H i j • q) * star (U.entry j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : I, ∑ _j : I, δ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [← sub_mul, ← mul_sub]
      calc
        _ ≤ ‖U.entry i‖ * ‖rowPair U.entry x i j - H i j • q‖ * ‖star (U.entry j)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1 * ‖rowPair U.entry x i j - H i j • q‖ * 1 := by
          gcongr
          · exact U.entry_norm_le i
          · simpa only [norm_star] using U.entry_norm_le j
        _ ≤ δ := by simpa only [one_mul, mul_one] using h i j
    _ = _ := by simp [pow_two]; ring

end ProjectionRow

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma selfAdjoint_covariance (a : D) : IsSelfAdjoint (a * star a) :=
  IsSelfAdjoint.mul_star_self a

omit [DecidableEq I] [Fintype I] in
lemma traceOneNorm_covariance_difference (τ : Pureness.TracialState D) {q a b : D}
    (hq : IsStarProjection q) (ha : a * q = a) (hb : b * q = b) :
    traceOneNorm τ (b * star b - a * star a) ≤
      (‖a‖ + ‖b‖) * ‖b - a‖ * (τ.functional q).re := by
  apply traceOneNorm_le_of_pairing τ ((selfAdjoint_covariance b).sub
    (selfAdjoint_covariance a))
  intro s _ hs
  have he : b * star b - a * star a =
      (b - a) * q * star b + a * q * (star b - star a) := by
    rw [sub_mul, hb, ha]
    noncomm_ring
  rw [he, mul_add, map_add, Complex.add_re]
  have hq0 : 0 ≤ (τ.functional q).re := (τ.functional.map_nonneg hq.nonneg).1
  have h1 : ‖τ.functional (s * ((b - a) * q * star b))‖ ≤
      ‖s‖ * (τ.functional q).re * (‖b - a‖ * ‖star b‖) := by
    simpa only [mul_assoc] using trace_sandwich_pairing_le τ hq s (b - a) (star b)
  have h2 : ‖τ.functional (s * (a * q * (star b - star a)))‖ ≤
      ‖s‖ * (τ.functional q).re * (‖a‖ * ‖star b - star a‖) := by
    simpa only [mul_assoc] using trace_sandwich_pairing_le τ hq s a (star b - star a)
  have hs1 : ‖s‖ * (τ.functional q).re ≤ (τ.functional q).re := by
    nlinarith [norm_nonneg s]
  have hb0 := norm_nonneg b
  have ha0 := norm_nonneg a
  have hd0 := norm_nonneg (b - a)
  have he1 := (Complex.re_le_norm (τ.functional (s * ((b - a) * q * star b)))).trans h1
  have he2 := (Complex.re_le_norm (τ.functional (s * (a * q * (star b - star a))))).trans h2
  rw [norm_star] at he1
  rw [← star_sub, norm_star] at he2
  simp only [star_sub] at he2
  nlinarith [mul_le_mul_of_nonneg_right hs1 (mul_nonneg hd0 hb0),
    mul_le_mul_of_nonneg_right hs1 (mul_nonneg ha0 hd0)]

omit [DecidableEq I] in
lemma traceOneNorm_sum_le (τ : Pureness.TracialState D) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) :
    traceOneNorm τ (∑ i, a i) ≤ ∑ i, traceOneNorm τ (a i) := by
  apply traceOneNorm_le_of_pairing τ (isSelfAdjoint_sum _ fun i _ => ha i)
  intro s hs hsn
  simp only [Finset.mul_sum, map_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun i _ => trace_selfAdjoint_contraction_mul_le τ hs (ha i) hsn

omit [DecidableEq I] in
lemma row_covariance_trace_error (τ : Pureness.TracialState D) {q : D}
    (hq : IsStarProjection q) (a b : I → D)
    (ha : ∀ i, a i * q = a i) (hb : ∀ i, b i * q = b i) {M N δ : ℝ}
    (hM : ∀ i, ‖a i‖ ≤ M) (hN : ∀ i, ‖b i‖ ≤ N)
    (hδ : ∀ i, ‖b i - a i‖ ≤ δ) :
    traceOneNorm τ ((∑ i, b i * star (b i)) - ∑ i, a i * star (a i)) ≤
      (Fintype.card I : ℝ) * (M + N) * δ * (τ.functional q).re := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, traceOneNorm τ (b i * star (b i) - a i * star (a i)) :=
      traceOneNorm_sum_le τ _ fun i => (selfAdjoint_covariance _).sub (selfAdjoint_covariance _)
    _ ≤ ∑ _i : I, (M + N) * δ * (τ.functional q).re := Finset.sum_le_sum fun i _ => by
      apply (traceOneNorm_covariance_difference τ hq (ha i) (hb i)).trans
      have hMN : 0 ≤ M + N := add_nonneg ((norm_nonneg _).trans (hM i)) ((norm_nonneg _).trans (hN i))
      gcongr
      · exact (τ.functional.map_nonneg hq.nonneg).1
      · exact hM i
      · exact hN i
      · exact hδ i
    _ = _ := by simp; ring

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma rowPair_perturb (a b c d x : D) {E F M N : ℝ}
    (hab : ‖a - b‖ ≤ E) (hcd : ‖c - d‖ ≤ F) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ N)
    (hx : ‖x‖ ≤ 1) :
    ‖star a * x * c - star b * x * d‖ ≤ E * N + M * F := by
  have hE : 0 ≤ E := (norm_nonneg _).trans hab
  have hM : 0 ≤ M := (norm_nonneg _).trans hb
  have he : star a * x * c - star b * x * d =
      star (a - b) * x * c + star b * x * (c - d) := by
    rw [star_sub]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖star (a - b) * x * c‖ + ‖star b * x * (c - d)‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ * ‖x‖ * ‖c‖ + ‖b‖ * ‖x‖ * ‖c - d‖ := by
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr; simpa only [norm_star] using norm_mul_le (star (a - b)) x)
      · exact (norm_mul_le _ _).trans (by gcongr; simpa only [norm_star] using norm_mul_le (star b) x)
    _ ≤ E * 1 * N + M * 1 * F := by gcongr
    _ = _ := by ring

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma rowPair_real_scale (a : I → D) (r : I → ℝ) (x : D) (i j : I) :
    rowPair (fun k => r k • a k) x i j = (r i * r j) • rowPair a x i j := by
  simp only [rowPair, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (r j) (r i)]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma rowPair_scale_error {q : D} (a : I → D) (r : I → ℝ) (x : D)
    (H : Matrix I I ℂ) {L δ : ℝ} (hr : ∀ i, 0 ≤ r i) (hL : ∀ i, r i ≤ L)
    (h : ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ δ) (i j : I) :
    ‖rowPair (fun k => r k • a k) x i j - ((r i * r j) • H i j) • q‖ ≤ L ^ 2 * δ := by
  rw [rowPair_real_scale, smul_assoc, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hr i) (hr j))]
  have hL0 : 0 ≤ L := (hr i).trans (hL i)
  calc
    _ ≤ (L * L) * ‖rowPair a x i j - H i j • q‖ := by
      gcongr
      · exact hr j
      · exact hL i
      · exact hL j
    _ ≤ (L * L) * δ := mul_le_mul_of_nonneg_left (h i j) (mul_self_nonneg L)
    _ = _ := by ring

theorem normalize_weighted_row {q : D} (hq : IsStarProjection q)
    (b : I → D) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hb : ∀ i, b i * q = b i) {L M δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hinv : ∀ i, (ρ i)⁻¹ ≤ L) (hbn : ∀ i, ‖b i‖ ≤ M)
    (hg : ∀ i j, ‖star (b i) * b j - (if i = j then (ρ i) ^ 2 • q else 0)‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * (L ^ 2 * δ) ≤ 1 / 2) :
    ∃ U : ProjectionRow I q,
      (∀ i, ‖U.entry i - (ρ i)⁻¹ • b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * L ^ 3 * M * δ) ∧
      (∀ i, ‖ρ i • U.entry i - b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * L ^ 3 * M * δ) := by
  let a : I → D := fun i => (ρ i)⁻¹ • b i
  have hasupp (i : I) : a i * q = a i := by simp only [a, smul_mul_assoc, hb]
  have han (i : I) : ‖a i‖ ≤ L * M := by
    rw [show a i = (ρ i)⁻¹ • b i from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (inv_pos.mpr (hρ i)))]
    exact mul_le_mul (hinv i) (hbn i) (norm_nonneg _) hL
  have hag (i j : I) : ‖star (a i) * a j - (if i = j then q else 0)‖ ≤ L ^ 2 * δ := by
    have he : star (a i) * a j - (if i = j then q else 0) =
        ((ρ i)⁻¹ * (ρ j)⁻¹) •
          (star (b i) * b j - (if i = j then (ρ i) ^ 2 • q else 0)) := by
      simp only [a, star_smul, star_trivial, smul_mul_smul_comm, smul_sub]
      congr 1
      by_cases hij : i = j
      · subst j
        simp only [ite_true, smul_smul]
        rw [show (ρ i)⁻¹ * (ρ i)⁻¹ * (ρ i) ^ 2 = 1 by field_simp [ne_of_gt (hρ i)]]
        rw [one_smul]
      · simp only [ite_eq_right hij, smul_zero]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (inv_pos.mpr (hρ i)))
      (le_of_lt (inv_pos.mpr (hρ j))))]
    calc
      _ ≤ (L * L) * ‖star (b i) * b j - (if i = j then (ρ i) ^ 2 • q else 0)‖ := by
        gcongr
        · exact le_of_lt (inv_pos.mpr (hρ j))
        · exact hinv i
        · exact hinv j
      _ ≤ (L * L) * δ := mul_le_mul_of_nonneg_left (hg i j) (mul_self_nonneg L)
      _ = _ := by ring
  obtain ⟨U, hU⟩ := normalize_almost_row hq a hasupp hag hsmall
  have hsum : (∑ j, ‖a j‖) ≤ (Fintype.card I : ℝ) * (L * M) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) fun j _ => han j
  have hU' (i : I) : ‖U.entry i - a i‖ ≤
      2 * (Fintype.card I : ℝ) ^ 3 * L ^ 3 * M * δ := by
    apply (hU i).trans
    calc
      _ ≤ 2 * ((Fintype.card I : ℝ) * (L * M)) * (Fintype.card I : ℝ) ^ 2 * (L ^ 2 * δ) := by
        gcongr
      _ = _ := by ring
  refine ⟨U, hU', fun i => ?_⟩
  have he : ρ i • U.entry i - b i = ρ i • (U.entry i - a i) := by
    rw [smul_sub]
    simp only [a, smul_smul, mul_inv_cancel₀ (ne_of_gt (hρ i)), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (hρ i)]
  exact (mul_le_mul_of_nonneg_right (hρ1 i) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hU' i)

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma normalized_rowPair_error {q : D} (U : ProjectionRow I q)
    (b : I → D) (r : I → ℝ) (x : D) (hx : ‖x‖ ≤ 1) (H : Matrix I I ℂ)
    {L M E δ : ℝ} (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L) (hri : ∀ i, r i ≤ L)
    (hbn : ∀ i, ‖b i‖ ≤ M)
    (hU : ∀ i, ‖U.entry i - r i • b i‖ ≤ E)
    (h : ∀ i j, ‖rowPair b x i j - H i j • q‖ ≤ δ) (i j : I) :
    ‖rowPair U.entry x i j - ((r i * r j) • H i j) • q‖ ≤
      E * (1 + L * M) + L ^ 2 * δ := by
  have han : ‖r i • b i‖ ≤ L * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr i)]
    exact mul_le_mul (hri i) (hbn i) (norm_nonneg _) hL
  have hp := rowPair_perturb (U.entry i) (r i • b i) (U.entry j) (r j • b j) x
    (hU i) (hU j) han (U.entry_norm_le j) hx
  have hscale := rowPair_scale_error b r x H hr hri h i j
  calc
    _ ≤ ‖rowPair U.entry x i j - rowPair (fun k => r k • b k) x i j‖ +
        ‖rowPair (fun k => r k • b k) x i j - ((r i * r j) • H i j) • q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (E * 1 + (L * M) * E) + L ^ 2 * δ := add_le_add hp hscale
    _ = _ := by ring

end

section

open scoped ComplexOrder

section RowSubmatrix

variable {I : Type uI} {J : Type uJ} {D : Type uD} [Fintype I] [Fintype J] [CStarAlgebra D]

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

omit [Fintype J] in
lemma atom_eq_coeff (i : I) : U.atom i = U.coeff q i i := by
  simp only [atom, coeff, U.right_support]

omit [Fintype J] in
lemma atom_projection (i : I) : IsStarProjection (U.atom i) := by
  classical
  rw [U.atom_eq_coeff]
  constructor
  · change U.coeff q i i * U.coeff q i i = U.coeff q i i
    rw [U.coeff_mul q q U.projection.isIdempotentElem, ite_eq_left rfl,
      U.projection.isIdempotentElem]
  · change star (U.coeff q i i) = U.coeff q i i
    rw [U.coeff_star, U.projection.isSelfAdjoint.star_eq]

omit [Fintype J] in
lemma atom_orthogonal : Pairwise (fun i j => U.atom i * U.atom j = 0) := by
  classical
  intro i j hij
  rw [U.atom_eq_coeff, U.atom_eq_coeff, U.coeff_mul q q U.projection.isIdempotentElem,
    ite_eq_right hij]

lemma subrow_range (f : J ↪ I) : (U.subrow f).sample q = ∑ i, U.atom (f i) :=
  (U.subrow f).range_eq_sum

omit [Fintype J] in
lemma upper_cut_subrow [LinearOrder I] (j : I) :
    upperLayerCut U.atom j =
      (U.subrow (Function.Embedding.subtype (j ≤ ·))).sample q := by
  classical
  rw [U.subrow_range, upperLayerCut]
  simp only [cutCoefficient, ite_smul, one_smul, zero_smul]
  exact by simpa only [Finset.subtype_univ, Finset.sum_filter, Function.Embedding.subtype_apply] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := (j ≤ ·)) U.atom).symm

end ProjectionRow

end RowSubmatrix

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma rowPair_spectral_rotation {q : D} (f : D →ₚ[ℂ] ℂ) (a : I → D) {δ : ℝ}
    (h : ∀ i j, ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ δ) (i j : I) :
    ‖star (rotateRow a (scalarRowGram_posSemidef f a).isHermitian.eigenvectorUnitary i) *
        rotateRow a (scalarRowGram_posSemidef f a).isHermitian.eigenvectorUnitary j -
      (if i = j then
        (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i • q else 0)‖ ≤
      (Fintype.card I : ℝ) ^ 2 * δ := by
  let hG := (scalarRowGram_posSemidef f a).isHermitian
  have he := hG.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_star_apply] at he
  have hr := rowPair_rotate_error a hG.eigenvectorUnitary 1 (scalarRowGram f a) h i j
  rw [he] at hr
  simpa only [rowPair, mul_one, Matrix.diagonal_apply, Function.comp_apply, ite_smul,
    zero_smul, RCLike.ofReal_eq_complex_ofReal, Complex.coe_smul] using hr

end

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [Fintype I] in
lemma traceOneNorm_of_nonneg (τ : Pureness.TracialState D) {a : D} (ha : 0 ≤ a) :
    traceOneNorm τ a = (τ.functional a).re := by
  rw [traceOneNorm, CFC.abs_of_nonneg a ha]

omit [Fintype I] in
lemma covariance_trace_le_of_gram {q b : D} (hq : IsStarProjection q)
    (hb : b * q = b) {c δ : ℝ} (hg : ‖star b * b - c • q‖ ≤ δ)
    (τ : Pureness.TracialState D) :
    (τ.functional (b * star b)).re ≤ (c + δ) * (τ.functional q).re := by
  have hqs : q * star b = star b := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hb
  have hsup : q * (star b * b - c • q) = star b * b - c • q := by
    rw [mul_sub, ← mul_assoc, hqs, mul_smul_comm, hq.isIdempotentElem]
  have hv := (Complex.re_le_norm (τ.functional (star b * b - c • q))).trans
    ((trace_supported_norm_le τ hq hsup).trans
      (mul_le_mul_of_nonneg_right hg (τ.functional.map_nonneg hq.nonneg).1))
  simp only [map_sub, τ.functional.map_smul_of_tower, Complex.sub_re,
    Complex.smul_re, smul_eq_mul] at hv
  rw [τ.tracial b (star b)]
  linarith

lemma covariance_nonneg (a : I → D) : 0 ≤ ∑ i, a i * star (a i) :=
  Finset.sum_nonneg fun i _ => mul_star_self_nonneg (a i)

lemma covariance_selfAdjoint (a : I → D) : IsSelfAdjoint (∑ i, a i * star (a i)) :=
  .of_nonneg (covariance_nonneg a)

lemma dropped_covariance_trace {q : D} (hq : IsStarProjection q) (b : I → D)
    (hb : ∀ i, b i * q = b i) (c : I → ℝ) {σ δ : ℝ}
    (hc : ∀ i, c i ≤ σ) (hg : ∀ i, ‖star (b i) * b i - c i • q‖ ≤ δ)
    (τ : Pureness.TracialState D) :
    traceOneNorm τ (∑ i, b i * star (b i)) ≤
      (Fintype.card I : ℝ) * (σ + δ) * (τ.functional q).re := by
  rw [traceOneNorm_of_nonneg τ (covariance_nonneg b), map_sum, Complex.re_sum]
  calc
    _ ≤ ∑ _i : I, (σ + δ) * (τ.functional q).re := Finset.sum_le_sum fun i _ => by
      apply (covariance_trace_le_of_gram hq (hb i) (hg i) τ).trans
      exact mul_le_mul_of_nonneg_right (by linarith [hc i])
        (τ.functional.map_nonneg hq.nonneg).1
    _ = _ := by simp; ring

lemma covariance_retain_error (τ : Pureness.TracialState D) {q : D}
    (hq : IsStarProjection q) (a : I → D) (p : I → Prop) [DecidablePred p]
    (b : {i // p i} → D) (ha : ∀ i, a i * q = a i)
    (hb : ∀ i, b i * q = b i) {M N E σ δ : ℝ}
    (hM : ∀ i, ‖a i‖ ≤ M) (hN : ∀ i, ‖b i‖ ≤ N)
    (hdist : ∀ i, ‖b i - a i‖ ≤ E) (c : I → ℝ)
    (hdrop : ∀ i, ¬p i → c i ≤ σ)
    (hgram : ∀ i, ‖star (a i) * a i - c i • q‖ ≤ δ) :
    traceOneNorm τ ((∑ i, b i * star (b i)) - ∑ i, a i * star (a i)) ≤
      ((Fintype.card {i // p i} : ℝ) * (M + N) * E +
        (Fintype.card {i // ¬p i} : ℝ) * (σ + δ)) * (τ.functional q).re := by
  have he := Fintype.sum_subtype_add_sum_subtype p (fun i => a i * star (a i))
  have hmain := row_covariance_trace_error τ hq (fun i : {i // p i} => a i) b
    (fun i => ha i) hb (fun i => hM i) hN hdist
  have htail := dropped_covariance_trace hq (fun i : {i // ¬p i} => a i)
    (fun i => ha i) (fun i => c i) (fun i => hdrop i i.property)
    (fun i => hgram i) τ
  rw [← he]
  have hsplit : (∑ i, b i * star (b i)) -
      ((∑ i : {i // p i}, a i * star (a i)) + ∑ i : {i // ¬p i}, a i * star (a i)) =
      ((∑ i, b i * star (b i)) - ∑ i : {i // p i}, a i * star (a i)) +
        -(∑ i : {i // ¬p i}, a i * star (a i)) := by abel
  rw [hsplit]
  apply (traceOneNorm_add_le τ ((covariance_selfAdjoint b).sub
    (covariance_selfAdjoint _)) (covariance_selfAdjoint _).neg).trans
  rw [traceOneNorm_neg]
  nlinarith

end

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem normalize_retained_spectrum {q : D} (hq : IsStarProjection q)
    (b : I → D) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hb : ∀ i, b i * q = b i) {σ M δ : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hbn : ∀ i, ‖b i‖ ≤ M)
    (hg : ∀ i j, ‖star (b i) * b j - (if i = j then c i • q else 0)‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 * δ) ≤ 1 / 2) :
    ∃ U : ProjectionRow {i : I // σ ≤ c i} q,
      (∀ i, ‖U.entry i - (Real.sqrt (c i))⁻¹ • b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ) ∧
      (∀ i : {i : I // σ ≤ c i}, ‖Real.sqrt (c i) • U.entry i - b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ) := by
  classical
  let J := {i : I // σ ≤ c i}
  have hcard : (Fintype.card J : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i => σ ≤ c i)
  have hL : 0 ≤ (Real.sqrt σ)⁻¹ := le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hσ))
  have hρ (i : J) : 0 < Real.sqrt (c i) := Real.sqrt_pos.mpr (hσ.trans_le i.property)
  have hρ1 (i : J) : Real.sqrt (c i) ≤ 1 := Real.sqrt_le_one.mpr (hc1 i)
  have hinv (i : J) : (Real.sqrt (c i))⁻¹ ≤ (Real.sqrt σ)⁻¹ :=
    inv_le_inv₀ (hρ i) (Real.sqrt_pos.mpr hσ) |>.mpr (Real.sqrt_le_sqrt i.property)
  have hgs (i j : J) :
      ‖star (b i) * b j - (if i = j then (Real.sqrt (c i)) ^ 2 • q else 0)‖ ≤ δ := by
    have he : (i = j) ↔ (i.val = j.val) := Subtype.ext_iff
    simpa only [Real.sq_sqrt (hc i), he] using hg i j
  have hsmallJ : (Fintype.card J : ℝ) ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 * δ) ≤ 1 / 2 := by
    apply le_trans ?_ hsmall
    gcongr
  obtain ⟨U, hU, hW⟩ := normalize_weighted_row hq (fun i : J => b i)
    (fun i => Real.sqrt (c i)) hρ hρ1 (fun i => hb i) hL hδ hinv (fun i => hbn i) hgs hsmallJ
  have hE : 2 * (Fintype.card J : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ ≤
      2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ := by gcongr
  exact ⟨U, fun i => (hU i).trans hE, fun i => (hW i).trans hE⟩

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma covariance_scaled_row {q : D} (U : ProjectionRow I q) (c : I → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (∑ i, (Real.sqrt (c i) • U.entry i) * star (Real.sqrt (c i) • U.entry i)) =
      ∑ i, c i • U.atom i := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_smul, star_trivial, smul_mul_smul_comm, ProjectionRow.atom]
  rw [← pow_two, Real.sq_sqrt (hc i)]

omit [DecidableEq I] in
lemma retained_spectrum_trace_error {q : D} (hq : IsStarProjection q)
    (b : I → D) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hb : ∀ i, b i * q = b i) {σ M E δ : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hσδ : 0 ≤ σ + δ) (hbn : ∀ i, ‖b i‖ ≤ M)
    (hg : ∀ i, ‖star (b i) * b i - c i • q‖ ≤ δ)
    (U : ProjectionRow {i : I // σ ≤ c i} q)
    (hU : ∀ i : {i : I // σ ≤ c i}, ‖Real.sqrt (c i) • U.entry i - b i‖ ≤ E)
    (τ : Pureness.TracialState D) :
    traceOneNorm τ ((∑ i : {i : I // σ ≤ c i}, c i • U.atom i) - ∑ i, b i * star (b i)) ≤
      ((Fintype.card I : ℝ) * ((M + 1) * E + (σ + δ))) * (τ.functional q).re := by
  classical
  have hnorm (i : {i : I // σ ≤ c i}) : ‖Real.sqrt (c i) • U.entry i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul (Real.sqrt_le_one.mpr (hc1 i)) (U.entry_norm_le i)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hsupp (i : {i : I // σ ≤ c i}) : (Real.sqrt (c i) • U.entry i) * q =
      Real.sqrt (c i) • U.entry i := by rw [smul_mul_assoc, U.right_support]
  have he := covariance_retain_error τ hq b (fun i => σ ≤ c i)
    (fun i => Real.sqrt (c i) • U.entry i) hb hsupp hbn hnorm hU c
    (fun i hi => (lt_of_not_ge hi).le) hg
  rw [covariance_scaled_row U (fun i => c i) (fun i => hc i)] at he
  apply he.trans
  have hk : (Fintype.card {i : I // σ ≤ c i} : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i => σ ≤ c i)
  have hd : (Fintype.card {i : I // ¬σ ≤ c i} : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i => ¬σ ≤ c i)
  apply mul_le_mul_of_nonneg_right ?_ (τ.functional.map_nonneg hq.nonneg).1
  nlinarith [mul_le_mul_of_nonneg_right hk (mul_nonneg (by linarith : 0 ≤ M + 1) hE),
    mul_le_mul_of_nonneg_right hd hσδ]

end

open scoped ComplexOrder

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uE uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [CStarAlgebra D]

lemma sortedIndex_monotone (c : I → ℝ) : Monotone (c ∘ sortedIndex c) :=
  Tuple.monotone_sort (c ∘ (Fintype.equivFin I).symm)

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

lemma sorted_weighted_sum (c : I → ℝ) :
    ∑ i, c (sortedIndex c i) • (U.sorted c).atom i = ∑ i, c i • U.atom i := by
  exact (sortedIndex c).sum_comp (fun i => c i • U.atom i)

lemma layer_sum {n : ℕ} (U : ProjectionRow (Fin n) q) (c : Fin n → ℝ) :
    ∑ j, orderedLayerWeights c j • upperLayerCut U.atom j = ∑ i, c i • U.atom i := by
  rw [layer_decomposition]
  simp only [layerCoefficient_orderedLayerWeights]

lemma subrow_entry_error {J : Type uJ} [Fintype J] (e : J ↪ I) (x : D)
    (H : Matrix I I ℂ) {δ : ℝ}
    (h : ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤ δ) :
    ∀ i j, ‖rowPair (U.subrow e).entry x i j - H (e i) (e j) • q‖ ≤ δ :=
  fun i j => h (e i) (e j)

lemma subrow_compression {J : Type uJ} [Fintype J] (e : J ↪ I) (x : D)
    (H : Matrix I I ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤ δ) :
    ‖(U.subrow e).sample q * x * (U.subrow e).sample q -
      (U.subrow e).matrix q (H.submatrix e e)‖ ≤ (Fintype.card I : ℝ) ^ 2 * δ := by
  classical
  apply ((U.subrow e).compression_norm_le x (H.submatrix e e)
    (U.subrow_entry_error e x H h)).trans
  have hcard : (Fintype.card J : ℝ) ≤ (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  gcongr

end ProjectionRow

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceOneNorm_unitary_conjugate (τ : Pureness.TracialState D) (x : unitary D) (a : D) :
    traceOneNorm τ ((x : D) * a * star (x : D)) = traceOneNorm τ a := by
  have he : star ((x : D) * a * star (x : D)) * ((x : D) * a * star (x : D)) =
      (x : D) * (star a * a) * star (x : D) := by
    simp only [star_mul, star_star, mul_assoc, ← mul_assoc (star (x : D)) (x : D),
      x.property.1, one_mul]
  dsimp only [traceOneNorm, CFC.abs]
  rw [he, sqrt_unitary_conjugate (star_mul_self_nonneg a), trace_unitary_conjugate]

lemma trace_re_le_oneNorm (τ : Pureness.TracialState D) {a : D} (ha : IsSelfAdjoint a) :
    (τ.functional a).re ≤ traceOneNorm τ a := by
  simpa only [one_mul] using
    trace_selfAdjoint_contraction_mul_le τ (IsSelfAdjoint.one D) ha (IsStarProjection.one D).norm_le

lemma trace_mass_perturb (τ : Pureness.TracialState D) {b h : D}
    (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) {ε t : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε) (hmass : (τ.functional h).re ≤ t) :
    (τ.functional b).re ≤ t + ε := by
  have ht := (trace_re_le_oneNorm τ (hb.sub hh)).trans hclose
  simp only [map_sub, Complex.sub_re] at ht
  linarith

lemma trace_central_perturb (τ : Pureness.TracialState D) {b h : D}
    (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) (x : unitary D) {ε μ : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε)
    (hcentral : traceOneNorm τ (h - (x : D) * h * star (x : D)) ≤ μ) :
    traceOneNorm τ (b - (x : D) * b * star (x : D)) ≤ 2 * ε + μ := by
  have he : b - (x : D) * b * star (x : D) =
      ((b - h) + (h - (x : D) * h * star (x : D))) +
        (x : D) * (h - b) * star (x : D) := by noncomm_ring
  rw [he]
  have htriangle := traceOneNorm_add_le τ ((hb.sub hh).add (hh.sub (hh.conjugate (x : D))))
    ((hh.sub hb).conjugate (x : D))
  have htriangle' := traceOneNorm_add_le τ (hb.sub hh) (hh.sub (hh.conjugate (x : D)))
  have hrev : traceOneNorm τ (h - b) = traceOneNorm τ (b - h) := by
    rw [← neg_sub b h, traceOneNorm_neg]
  rw [traceOneNorm_unitary_conjugate, hrev] at htriangle
  linarith

end

section

lemma block_tolerances (m : ℝ) (hm : 0 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∃ σ δ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < δ ∧
      m ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 * (m ^ 2 * δ)) ≤ 1 / 2 ∧
      m * ((m + 1) * (2 * m ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * m * (m ^ 2 * δ)) +
        (σ + m ^ 2 * δ)) ≤ η ^ 2 ∧
      m ^ 2 * ((2 * m ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * m * (m ^ 2 * δ)) *
        (1 + (Real.sqrt σ)⁻¹ * m) + (Real.sqrt σ)⁻¹ ^ 2 * (m ^ 2 * δ)) < η := by
  obtain ⟨σ₀, hσ₀, hσm⟩ := exists_pos_mul_lt (half_pos (sq_pos_of_pos hη)) m
  let σ := min σ₀ (1 / 2)
  have hσ : 0 < σ := lt_min hσ₀ (by norm_num)
  have hσ1 : σ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hσm' : m * σ < η ^ 2 / 2 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hm).trans_lt hσm
  let L := (Real.sqrt σ)⁻¹
  let E := 2 * m ^ 3 * L ^ 3 * m * m ^ 2
  let A := m ^ 2 * (L ^ 2 * m ^ 2)
  let B := m * ((m + 1) * E + m ^ 2)
  let C := m ^ 2 * (E * (1 + L * m) + L ^ 2 * m ^ 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨δ₁, hδ₁, he₁⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 2) A
  obtain ⟨δ₂, hδ₂, he₂⟩ := exists_pos_mul_lt (half_pos (sq_pos_of_pos hη)) B
  obtain ⟨δ₃, hδ₃, he₃⟩ := exists_pos_mul_lt hη C
  let δ := min δ₁ (min δ₂ δ₃)
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hd3 : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hhA : A * δ < 1 / 2 := (mul_le_mul_of_nonneg_left hd1 hA).trans_lt he₁
  have hhB : B * δ < η ^ 2 / 2 := (mul_le_mul_of_nonneg_left hd2 hB).trans_lt he₂
  have hhC : C * δ < η := (mul_le_mul_of_nonneg_left hd3 hC).trans_lt he₃
  refine ⟨σ, δ, hσ, hσ1, lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_, ?_, ?_⟩
  · calc
      _ = A * δ := by dsimp [A, L]; ring
      _ ≤ 1 / 2 := hhA.le
  · have hh : B * δ + m * σ ≤ η ^ 2 := by linarith
    calc
      _ = B * δ + m * σ := by dsimp [B, E, L]; ring
      _ ≤ η ^ 2 := hh
  · calc
      _ = C * δ := by dsimp [C, E, L]; ring
      _ < η := hhC

open scoped ComplexOrder

lemma exists_blockControl (m : ℝ) (hm : 0 ≤ m) {η : ℝ} (hη : 0 < η) :
    Nonempty (BlockControl m η) := by
  obtain ⟨σ, δ, hσ, hσ1, hδ, hInv, htr, hcomp⟩ := block_tolerances m hm hη
  exact ⟨⟨σ, δ, hσ, hσ1, hδ, hInv, htr, hcomp⟩⟩

lemma rowCompressionError_nonneg {m σ δ : ℝ} (hm : 0 ≤ m) (hδ : 0 ≤ δ) :
    0 ≤ rowCompressionError m σ δ := by
  dsimp [rowCompressionError, rowCorrectionError]
  positivity

end

variable {D : Type uD} [CStarAlgebra D] {q : D} {n : ℕ}

lemma upperColumn_nonempty (j : Fin n) : 0 < Fintype.card {i : Fin n // j ≤ i} := by
  let : Nonempty {i : Fin n // j ≤ i} := ⟨⟨j, le_rfl⟩⟩
  exact Fintype.card_pos

namespace ProjectionRow

omit [CStarAlgebra D] in
lemma sum_pos_weights {I : Type uI} [Fintype I] {E : Type uE}
    [AddCommMonoid E] [Module ℝ E] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (a : I → E) :
    ∑ i : {i : I // 0 < w i}, w i • a i = ∑ i, w i • a i := by
  classical
  rw [Fintype.sum_subtype_add_sum_subtype (p := fun i => 0 < w i) (fun i => w i • a i) |>.symm]
  have hz : (∑ i : {i : I // ¬0 < w i}, w i • a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [le_antisymm (le_of_not_gt i.property) (hw i), zero_smul]
  rw [hz, add_zero]

variable (U : ProjectionRow (Fin n) q)

lemma upperEmbedding_range (j : Fin n) :
    (U.subrow (upperEmbedding j)).sample q = upperLayerCut U.atom j := by
  rw [U.subrow_range, U.upper_cut_subrow, U.subrow_range]
  exact (Fintype.equivFin {i : Fin n // j ≤ i}).symm.sum_comp
    (fun i => U.atom i.val)

lemma positive_layer_sum (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) :
    ∑ j : {j : Fin n // 0 < orderedLayerWeights c j},
      orderedLayerWeights c j • (U.subrow (upperEmbedding j)).sample q =
        ∑ i, c i • U.atom i := by
  simp_rw [U.upperEmbedding_range]
  rw [sum_pos_weights (orderedLayerWeights c) (orderedLayerWeights_nonneg c hc hm)]
  exact U.layer_sum c

variable [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing D] in
lemma positive_layer_energy (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (hm : Monotone c)
    (τ : Pureness.TracialState D) (x : D) :
    ∑ j : {j : Fin n // 0 < orderedLayerWeights c j}, orderedLayerWeights c j *
      traceTwoNorm τ (x * (U.subrow (upperEmbedding j)).sample q -
        (U.subrow (upperEmbedding j)).sample q * x) ^ 2 =
      ∑ j, orderedLayerWeights c j * traceTwoNorm τ
        (x * upperLayerCut U.atom j - upperLayerCut U.atom j * x) ^ 2 := by
  simp_rw [U.upperEmbedding_range]
  simpa only [smul_eq_mul] using
    sum_pos_weights (orderedLayerWeights c) (orderedLayerWeights_nonneg c hc hm)
      (fun j => traceTwoNorm τ (x * upperLayerCut U.atom j - upperLayerCut U.atom j * x) ^ 2)

end ProjectionRow

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.WeightedFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

attribute [instance] WeightedBlockFamily.indexFintype

omit [PartialOrder D] [StarOrderedRing D] in
lemma weightedAverage_sum {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : I → D) (a : J → D) :
    weightedAverage w v (∑ j, a j) = ∑ j, weightedAverage w v (a j) := by
  simp only [weightedAverage, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  exact Finset.sum_comm

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sum_le {I : Type uI} (s : Finset I) (τ : Pureness.TracialState D) (a : I → D) :
    traceTwoNorm τ (∑ i ∈ s, a i) ≤ ∑ i ∈ s, traceTwoNorm τ (a i) := by
  simpa only [traceTwoNorm_eq_gns, map_sum] using norm_sum_le s (fun i => τ.functional.toPreGNS (a i))

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PackingEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI uM

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_mass_difference_abs_le (τ : Pureness.TracialState D) {a : D} (ha : IsSelfAdjoint a) :
    |(τ.functional a).re| ≤ traceOneNorm τ a := by
  apply abs_le.mpr
  constructor
  · have h := trace_re_le_oneNorm τ ha.neg
    simp only [map_neg, Complex.neg_re, traceOneNorm_neg] at h
    linarith
  · exact trace_re_le_oneNorm τ ha

end

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TensorExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uR

noncomputable section

namespace Pureness

section

open scoped CStarAlgebra

variable {R : Type uR} {E : Type uE} {F : Type uF} [Ring R] [StarAddMonoid R] [Algebra ℂ R]

variable [CStarAlgebra E] [CStarAlgebra F]

variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] F)

variable (hf : DenseRange f) (hn : ∀ x, ‖g x‖ ≤ ‖f x‖)

lemma denseStarCompletionHom_apply (x : R) :
    denseStarCompletionHom f g hf hn (f x) = g x :=
  LinearMap.extendOfNorm_eq hf ⟨1, fun element => by
    simpa only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul] using hn element⟩ x

end

open scoped TensorProduct

universe u v

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

lemma IsNuclear.extendRepresentation_apply (hA : IsNuclear.{u,v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hfd : DenseRange f) (z : A ⊗[ℂ] B) :
    hA.extendRepresentation f g hf hfd (f z) = g z :=
  denseStarCompletionHom_apply f g hfd (hA.representation_norm_le f g hf) z

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.StateExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB uE

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace CurrentMain

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointFunctionalComplex_apply (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointFunctionalComplex f a = (f a : ℂ) := by
  have hr : ℜ (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [selfAdjointFunctionalComplex, hr, a.property.imaginaryPart]

lemma selfAdjointFunctional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hn : ‖f‖ ≤ 1) (h1 : f 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ f a := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖(a : A)‖ := norm_pos_iff.mpr (fun h => hz (Subtype.ext h))
  let b : selfAdjoint A := ‖(a : A)‖⁻¹ • a
  have hb0 : 0 ≤ (b : A) := smul_nonneg (by positivity) ha
  have hbn : ‖(b : A)‖ ≤ 1 := by
    change ‖‖(a : A)‖⁻¹ • (a : A)‖ ≤ 1
    simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hb1 : (b : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn
  have hsub : ‖(1 : selfAdjoint A) - b‖ ≤ 1 := by
    change ‖(1 : A) - (b : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hb1)).mpr
      (sub_le_self _ hb0)
  have hf : ‖f (1 - b)‖ ≤ 1 :=
    (f.le_opNorm _).trans ((mul_le_mul hn hsub (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hfb : 0 ≤ f b := by
    have := le_abs_self (f (1 - b))
    rw [map_sub, h1] at hf this
    change |1 - f b| ≤ 1 at hf
    linarith
  change 0 ≤ f (‖(a : A)‖⁻¹ • a) at hfb
  rw [map_smul, smul_eq_mul] at hfb
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp hfb

theorem state_extension (ι : A →⋆ₐ[ℂ] B) (hi : Function.Injective ι)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ∃ g : B →ₚ[ℂ] ℂ, g 1 = 1 ∧ ∀ a, g (ι a) = f a := by
  let L := selfAdjointEmbedding ι hi
  let F := stateRealContinuous f hf
  let E := L.equivRange
  let S : Submodule ℝ (selfAdjoint B) := L.range
  let _ : NormedAddCommGroup S := inferInstance
  let _ : NormedSpace ℝ S :=
    { norm_smul_le := fun r a => norm_smul_le r ((a : selfAdjoint B) : B) }
  let Fr : S →L[ℝ] ℝ := F.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hFr : ‖Fr‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change |(f (E.symm a)).re| ≤ 1 * ‖a‖
    simpa only [one_mul,E.symm.norm_map] using state_realPart_bound f hf (E.symm a)
  obtain ⟨G,hG,hGn⟩ := exists_extension_norm_eq S Fr
  have hGa (a : selfAdjoint A) : G (L a) = (f a).re := by
    have h := hG (E a)
    change G (L a) = F (E.symm (E a)) at h
    rw [E.symm_apply_apply] at h
    exact h
  have hG1 : G 1 = 1 := by
    have h := hGa 1
    have he : L 1 = 1 := Subtype.ext (map_one ι)
    rw [he] at h
    simpa [hf] using h
  let gL := selfAdjointFunctionalComplex G.toLinearMap
  have hgpos (b : B) (hb : 0 ≤ b) : 0 ≤ gL b := by
    have h := selfAdjointFunctional_nonneg G (hGn.le.trans hFr) hG1
      ⟨b,.of_nonneg hb⟩ hb
    change 0 ≤ selfAdjointFunctionalComplex G.toLinearMap
      ((⟨b,.of_nonneg hb⟩ : selfAdjoint B) : B)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast h
  let g : B →ₚ[ℂ] ℂ :=
    { toLinearMap := gL
      monotone' := by
        intro a b hab
        have h := hgpos (b-a) (sub_nonneg.mpr hab)
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  have hga (a : selfAdjoint A) : g (ι a) = f a := by
    change selfAdjointFunctionalComplex G.toLinearMap ((L a : selfAdjoint B) : B) = f a
    rw [selfAdjointFunctionalComplex_apply]
    change (G (L a) : ℂ) = f a
    rw [hGa]
    exact (Complex.ext rfl (by
      have hsa : IsSelfAdjoint (f a) := a.property.map f
      have he := congrArg Complex.im hsa
      simp only [Complex.star_def,Complex.conj_im] at he
      change 0 = (f a).im
      linarith))
  refine ⟨g, ?_, ?_⟩
  · have h := hga 1
    change g (ι 1) = f 1 at h
    simpa only [map_one,hf] using h
  · intro a
    have ha : a = (ℜ a : A) + Complex.I • (ℑ a : A) := by
      exact (realPart_add_I_smul_imaginaryPart a).symm
    conv_lhs => rw [ha]
    rw [map_add,map_smul,map_add,map_smul,hga,hga]
    rw [← map_smul,← map_add,← ha]

end CurrentMain

open scoped ComplexOrder InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpatialTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uE uF uH uK uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma spatialStarTensorHom_tmul (a : A) (b : B) :
    spatialStarTensorHom α β (a ⊗ₜ[ℂ] b)=spatialTensorOp (α a) (β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) = _
  rw [← spatialTensorOp_mul,mul_one,one_mul]

end Pureness

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma spatial_relation_coefficients_zero
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {ι : Type uι} (b : ι → B) (hb : LinearIndependent ℂ b)
    (s : Finset ι) (a : ι → A)
    (hz : spatialStarTensorHom α β (∑ i ∈ s, a i ⊗ₜ[ℂ] b i) = 0) :
    ∀ i ∈ s, a i = 0 := by
  classical
  have hc (x x' : H) : ∑ i ∈ s, ⟪x', α (a i) x⟫_ℂ • b i = 0 := by
    apply (map_eq_zero_iff β hβ).mp
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro y'
    have he := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
      ⟪((x' ⊗ₜ[ℂ] y' : H ⊗[ℂ] K) : SpatialHilbert H K), T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)⟫_ℂ) hz
    simpa only [map_sum, map_smul, spatialStarTensorHom_tmul,
      sum_apply, smul_apply,
      zero_apply, inner_zero_right, inner_sum, inner_smul_right,
      spatialTensorOp_coe, TensorProduct.mapL_tmul, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul] using he
  intro i hi
  apply (map_eq_zero_iff α hα).mp
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro x'
  rw [zero_apply, inner_zero_right]
  exact (linearIndependent_iff'.mp hb) s _ (hc x x') i hi

theorem spatialStarTensorHom_injective_of_faithful
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (spatialStarTensorHom α β) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ B
  obtain ⟨a, rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have ha := spatial_relation_coefficients_zero α β hα hβ b b.linearIndependent a.support a hz
  change ∑ i ∈ a.support, a i ⊗ₜ[ℂ] b i = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [ha i hi, TensorProduct.zero_tmul]

end Pureness

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
-- module Solutions.OAIQW_TracialSplitting.FaithfulRepresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uH uα uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

namespace Pureness

open scoped ComplexOrder InnerProductSpace

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma stateGNSVector_norm (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ‖stateGNSVector f‖ = 1 := by
  have h := f.preGNS_norm_sq (f.toPreGNS 1)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1] at h
  have h' : ‖f.toPreGNS 1‖ ^ 2 = 1 := by exact_mod_cast h
  have hnorm : ‖f.toPreGNS 1‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (h'.trans (one_pow 2).symm)
  simpa only [stateGNSVector, UniformSpace.Completion.norm_coe] using hnorm

lemma stateGNS_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (stateGNSVector f) = (f.toPreGNS a : f.GNS) := by
  simp [stateGNSVector, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

lemma stateGNS_vector_value (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪stateGNSVector f, f.gnsStarAlgHom a (stateGNSVector f)⟫_ℂ = f a := by
  rw [stateGNS_apply_vector]
  simp [stateGNSVector, UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

end Pureness

noncomputable section

namespace Pureness

open scoped ComplexOrder

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_positiveState_norming [Nontrivial A] (a : A) (ha : 0 ≤ a) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  have han : IsStarNormal a := (IsSelfAdjoint.of_nonneg ha).isStarNormal
  let s : spectrum ℂ a := ⟨(‖a‖ : ℂ), by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg ha)⟩
  let ev : C(spectrum ℂ a, ℂ) →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ (ContinuousMap.evalAlgHom ℂ ℂ s).toLinearMap (fun b hb => hb s)
  have hev : ev 1 = 1 := rfl
  obtain ⟨f, hf1, hf⟩ := CurrentMain.state_extension (cfcHom han)
    (cfcHom_injective han) ev hev
  refine ⟨f, hf1, ?_⟩
  calc
    f a = ev ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) := by
      simpa only [cfcHom_id] using hf ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
    _ = (‖a‖ : ℂ) := rfl

theorem positive_eq_zero_of_states [Nontrivial A] (a : A) (ha : 0 ≤ a)
    (h : ∀ f : A →ₚ[ℂ] ℂ, f 1 = 1 → f a = 0) : a = 0 := by
  obtain ⟨f, hf1, hfa⟩ := exists_positiveState_norming a ha
  have hn : (‖a‖ : ℂ) = 0 := hfa.symm.trans (h f hf1)
  exact norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hn)

theorem stateGNS_separates [Nontrivial A] (a : A)
    (h : ∀ f : A →ₚ[ℂ] ℂ, f 1 = 1 → f.gnsStarAlgHom a = 0) : a = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  apply positive_eq_zero_of_states (star a * a) (star_mul_self_nonneg a)
  intro f hf1
  rw [← stateGNS_vector_value f, map_mul, map_star, h f hf1, star_zero, mul_zero]
  simp

end Pureness

noncomputable section

namespace Pureness

open scoped InnerProductSpace ENNReal

variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] {H : ι → Type uH}

variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]

variable [∀ i, CompleteSpace (H i)]

variable (ρ : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))

lemma hilbertSumRepresentation_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSumRepresentation ρ a x i = ρ i a (x i) := rfl

lemma hilbertSumRepresentation_eq_iff (a b : A) :
    hilbertSumRepresentation ρ a = hilbertSumRepresentation ρ b ↔ ∀ i, ρ i a = ρ i b := by
  classical
  constructor
  · intro h i
    ext x
    have hh := congrArg (fun f : lp H 2 →L[ℂ] lp H 2 => f (lp.single 2 i x) i) h
    simpa only [hilbertSumRepresentation_apply, lp.single_apply, Pi.single_eq_same] using hh
  · intro h
    ext x i
    exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (h i)

end Pureness

noncomputable section

namespace Pureness

open scoped InnerProductSpace ComplexOrder

local instance instDecidableEq_solutions_r268d02_1 {α : Type uα} : DecidableEq α := Classical.decEq α
variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem universalStateGNS_injective : Function.Injective (universalStateGNS A) := by
  cases subsingleton_or_nontrivial A with
  | inl h => exact fun _ _ _ => Subsingleton.elim _ _
  | inr h =>
    apply (universalStateGNS A).toLinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply stateGNS_separates a
    intro f hf1
    have h := (hilbertSumRepresentation_eq_iff
      (fun g : PositiveStateIndex A => g.1.gnsStarAlgHom) a 0).mp
      (ha.trans (map_zero (universalStateGNS A)).symm) ⟨f, hf1⟩
    simpa only [map_zero] using h

end Pureness

noncomputable section

noncomputable section

namespace Pureness

variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem stateHilbertRepresentation_injective :
    Function.Injective (stateHilbertRepresentation A) := universalStateGNS_injective A

end Pureness

end

end

end

end

end

end

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
-- module Solutions.OAIQW_TracialSplitting.Hypertraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH uI


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

namespace NuclearTrace

open scoped InnerProductSpace ComplexOrder

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operator_le_of_unit_quadratic {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {c : ℝ} (h : ∀ ξ : H, ‖ξ‖ ≤ 1 → (⟪ξ, T ξ⟫_ℂ).re ≤ c) :
    T ≤ c • (1 : H →L[ℂ] H) := by
  have hc : 0 ≤ c := by simpa using h 0 (by simp)
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((IsSelfAdjoint.all c).smul (IsSelfAdjoint.one (H →L[ℂ] H))).sub hT, ?_⟩
  intro ξ
  by_cases hz : ξ = 0
  · subst ξ; change 0 ≤ (⟪(c • (1 : H →L[ℂ] H)-T) (0 : H),0⟫_ℂ).re; simp
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hz
  have hu : ‖(‖ξ‖⁻¹ : ℝ) • ξ‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have hb := h ((‖ξ‖⁻¹ : ℝ) • ξ) hu
  have he : (⟪(‖ξ‖⁻¹ : ℝ) • ξ, T ((‖ξ‖⁻¹ : ℝ) • ξ)⟫_ℂ).re =
      ‖ξ‖⁻¹ * ‖ξ‖⁻¹ * (⟪ξ,T ξ⟫_ℂ).re := by
    simp only [T.map_smul_of_tower,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
      Complex.smul_re,smul_eq_mul]
    ring
  rw [he] at hb
  have hb' : (⟪ξ,T ξ⟫_ℂ).re ≤ c * ‖ξ‖^2 := by
    have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖ξ‖)
    field_simp at hmul
    nlinarith
  change 0 ≤ (⟪(c • (1 : H →L[ℂ] H)-T) ξ,ξ⟫_ℂ).re
  simp only [sub_apply,smul_apply,
    one_apply_eq_self,inner_sub_left,inner_smul_left_eq_smul,
    Complex.sub_re,Complex.smul_re,smul_eq_mul,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow, Complex.ofReal_re]
  rw [show (⟪T ξ,ξ⟫_ℂ).re = (⟪ξ,T ξ⟫_ℂ).re from @inner_re_symm ℂ H _ _ _ (T ξ) ξ]
  linarith

end NuclearTrace

noncomputable section

namespace NuclearTrace

open scoped TensorProduct ComplexOrder InnerProductSpace

section CyclicExtension

variable {A B N H : Type} [CStarAlgebra A] [CStarAlgebra B]

variable [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem nuclear_cyclic_extension (hA : Pureness.IsNuclear.{0,0} A)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (π a) (ρ b)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (j : A ⊗[ℂ] B →⋆ₐ[ℂ] N) (hj : Function.Injective j) :
    ∃ σ : N →ₚ[ℂ] ℂ, σ 1 = 1 ∧
      ∀ a b, σ (j (a ⊗ₜ[ℂ] b)) = ⟪ξ,π a (ρ b ξ)⟫_ℂ := by
  let C : StarSubalgebra ℂ N := j.range.topologicalClosure
  let _ : IsClosed (C : Set N) := StarSubalgebra.isClosed_topologicalClosure _
  let _ : CStarAlgebra C := StarSubalgebra.cstarAlgebra C
  let _ : PartialOrder C := CStarAlgebra.spectralOrder C
  let _ : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let jC : A ⊗[ℂ] B →⋆ₐ[ℂ] C := j.codRestrict C
    (fun z => StarSubalgebra.le_topologicalClosure _ ⟨z,rfl⟩)
  have hjC : Function.Injective jC := fun x y h => hj (congrArg Subtype.val h)
  have hd : DenseRange jC := by
    have hd' : DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure j.range)) := by
      apply (denseRange_inclusion_iff _).mpr
      change closure (j.range : Set N) ⊆ closure (j.range : Set N)
      exact subset_rfl
    have hs : Function.Surjective j.rangeRestrict := by
      rintro ⟨x,z,hz⟩
      exact ⟨z,Subtype.ext hz⟩
    exact hd'.comp hs.denseRange (continuous_inclusion _)
  let L := hA.extendRepresentation jC (Pureness.commutingStarTensorHom π ρ hc) hjC hd
  let θ := vectorFunctional L ξ
  have hθ1 : θ 1 = 1 := by
    simp [θ,inner_self_eq_norm_sq_to_K,hξ]
  obtain ⟨σ,hσ1,hσ⟩ := CurrentMain.state_extension C.subtype Subtype.val_injective θ hθ1
  refine ⟨σ,hσ1,fun a b => ?_⟩
  rw [← show C.subtype (jC (a ⊗ₜ[ℂ] b)) = j (a ⊗ₜ[ℂ] b) from rfl,hσ]
  change ⟪ξ,L (jC (a ⊗ₜ[ℂ] b)) ξ⟫_ℂ = _
  rw [Pureness.IsNuclear.extendRepresentation_apply]
  rfl

end CyclicExtension

end NuclearTrace

end

end

end

end

end

end

end

end

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
-- module Solutions.OAIQW_TracialSplitting.VectorApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uH uI uV

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace NuclearTrace

section

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (f g : A →ₚ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)

variable (hfg : ∀ a : A, 0 ≤ a → (g a).re ≤ C * (f a).re)

lemma dominationGNS_norm_bound (x : f.GNS) :
    ‖dominationGNS f g hC hfg x‖ ≤ Real.sqrt C * ‖x‖ := by
  induction x using induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x => simpa using domination_preGNS_norm f g hC hfg (f.ofPreGNS x)

lemma dominationGNS_intertwines (a : A) :
    (dominationGNS f g hC hfg).comp (f.gnsStarAlgHom a) =
      (g.gnsStarAlgHom a).comp (dominationGNS f g hC hfg) := by
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS]

lemma dominationGNS_adjoint_intertwines (a : A) :
    (dominationGNS f g hC hfg).adjoint.comp (g.gnsStarAlgHom a) =
      (f.gnsStarAlgHom a).comp (dominationGNS f g hC hfg).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    (dominationGNS_intertwines f g hC hfg (star a))
  simpa only [ContinuousLinearMap.adjoint_comp,map_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using h.symm

lemma dominationDensity_nonneg : 0 ≤ dominationDensity f g hC hfg := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

lemma dominationDensity_le : dominationDensity f g hC hfg ≤ C • (1 : f.GNS →L[ℂ] f.GNS) := by
  apply sub_nonneg.mp
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((IsSelfAdjoint.all C).smul (IsSelfAdjoint.one _)).sub
    (dominationDensity_nonneg f g hC hfg).isSelfAdjoint, ?_⟩
  intro x
  have hb : ‖dominationGNS f g hC hfg x‖^2 ≤ C * ‖x‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x))).mpr
      (dominationGNS_norm_bound f g hC hfg x)
    rw [mul_pow,Real.sq_sqrt hC] at h
    exact h
  change 0 ≤ (⟪(C • (1 : f.GNS →L[ℂ] f.GNS) - dominationDensity f g hC hfg) x,x⟫_ℂ).re
  simp only [sub_apply,smul_apply,one_apply_eq_self,inner_sub_left,
    inner_smul_left_eq_smul,Complex.sub_re,Complex.smul_re,smul_eq_mul,
    dominationDensity,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow,Complex.ofReal_re]
  linarith

lemma dominationDensity_commutes (a : A) :
    Commute (dominationDensity f g hC hfg) (f.gnsStarAlgHom a) := by
  change (dominationDensity f g hC hfg).comp (f.gnsStarAlgHom a) =
    (f.gnsStarAlgHom a).comp (dominationDensity f g hC hfg)
  unfold dominationDensity
  rw [ContinuousLinearMap.comp_assoc,dominationGNS_intertwines,
    ← ContinuousLinearMap.comp_assoc,dominationGNS_adjoint_intertwines,
    ContinuousLinearMap.comp_assoc]

lemma dominationDensity_value (a : A) :
    ⟪(f.toPreGNS 1 : f.GNS),dominationDensity f g hC hfg
      (f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS))⟫_ℂ = g a := by
  unfold dominationDensity
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,
    PositiveLinearMap.preGNS_inner_def]

end

open scoped ComplexStarModule

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (f : A →ₚ[ℂ] ℂ) (l : selfAdjoint A →ₗ[ℝ] ℝ) (C : ℝ)

variable (hl : ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l a| ≤ C * (f a).re)

lemma realPerturbation_apply (a : A) : realPerturbation f l C hl a =
    (C : ℂ) • f a + selfAdjointComplexification l a := rfl

lemma realPerturbation_le {a : A} (ha : 0 ≤ a) :
    (realPerturbation f l C hl a).re ≤ (2*C) * (f a).re := by
  rw [realPerturbation_apply,
    selfAdjointComplexification_apply l (⟨a,ha.isSelfAdjoint⟩ : selfAdjoint A)]
  simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  linarith [hl ⟨a,ha.isSelfAdjoint⟩ ha,le_abs_self (l ⟨a,ha.isSelfAdjoint⟩)]

include hl in
theorem real_functional_in_commutant (hC : 0 ≤ C) :
    ∃ T : f.GNS →L[ℂ] f.GNS, IsSelfAdjoint T ∧
      (-C) • (1 : f.GNS →L[ℂ] f.GNS) ≤ T ∧ T ≤ C • (1 : f.GNS →L[ℂ] f.GNS) ∧
      (∀ a, Commute T (f.gnsStarAlgHom a)) ∧
      ∀ a : selfAdjoint A, l a =
        (⟪(f.toPreGNS 1 : f.GNS),T (f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS))⟫_ℂ).re := by
  let : Algebra ℝ (f.GNS →L[ℂ] f.GNS) := Algebra.complexToReal
  let : Module ℝ (f.GNS →L[ℂ] f.GNS) := Module.complexToReal _
  let g := realPerturbation f l C hl
  have hg : ∀ a : A, 0 ≤ a → (g a).re ≤ (2*C)*(f a).re :=
    fun _ ha => realPerturbation_le f l C hl ha
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC
  let R := dominationDensity f g h2C hg
  have hR0 : 0 ≤ R := dominationDensity_nonneg f g h2C hg
  have hRle : R ≤ (2*C) • (1 : f.GNS →L[ℂ] f.GNS) := dominationDensity_le f g h2C hg
  have hRsa : IsSelfAdjoint R := hR0.isSelfAdjoint
  refine ⟨R - C • (1 : f.GNS →L[ℂ] f.GNS),
    hRsa.sub ((IsSelfAdjoint.all C).smul (IsSelfAdjoint.one _)), ?_, ?_, ?_, ?_⟩
  · simpa only [zero_sub,neg_smul] using sub_le_sub_right hR0 (C • (1 : f.GNS →L[ℂ] f.GNS))
  · apply (sub_le_iff_le_add).mpr
    simpa only [two_mul, add_smul] using hRle
  · intro a
    have hR := dominationDensity_commutes f g h2C hg a
    exact hR.sub_left ((Commute.one_left _).smul_left C)
  · intro a
    have hval := dominationDensity_value f g h2C hg (a : A)
    change (⟪(f.toPreGNS 1 : f.GNS),R (f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS))⟫_ℂ) = g a at hval
    have hfval : (⟪(f.toPreGNS 1 : f.GNS),f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS)⟫_ℂ) = f a := by
      simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,
        PositiveLinearMap.preGNS_inner_def]
    simp only [sub_apply,smul_apply,one_apply_eq_self,inner_sub_right,
      inner_smul_right_eq_smul,Complex.sub_re,Complex.smul_re,smul_eq_mul,hval,hfval]
    change l a = ((C : ℂ) • f a + selfAdjointComplexification l a).re - C * (f a).re
    rw [selfAdjointComplexification_apply]
    simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    ring

end NuclearTrace

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.CoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uE uK uN


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

namespace NuclearTrace

section GNSDensity

variable {A : Type uA} {K : Type uK} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (f : A →ₚ[ℂ] ℂ)

lemma algebraTensorVector_dense : DenseRange (algebraTensorVector (K := K) f) := by
  let M := (algebraTensorVector (K := K) f).range.topologicalClosure
  have hmem (k : K) (h : f.GNS) :
      (((k ⊗ₜ[ℂ] h : K ⊗[ℂ] f.GNS) : SpatialHilbert K f.GNS)) ∈ M := by
    induction h using UniformSpace.Completion.induction_on with
    | hp =>
      apply ((algebraTensorVector (K := K) f).range.isClosed_topologicalClosure).preimage
      fun_prop
    | ih h =>
      apply Submodule.le_topologicalClosure
      exact ⟨k ⊗ₜ[ℂ] f.ofPreGNS h,by simp⟩
  intro z
  change z ∈ M
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact (algebraTensorVector (K := K) f).range.isClosed_topologicalClosure
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | (rw [UniformSpace.Completion.coe_zero]; exact zero_mem _) | simp
    | tmul k h => exact hmem k h
    | add z w hz hw => simpa only [coe_add] using M.add_mem hz hw

end GNSDensity

section CoefficientValue

variable {A : Type uA} {K : Type uK} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (f : A →ₚ[ℂ] ℂ)

variable (T : f.GNS →L[ℂ] f.GNS) (hT : ∀ a, Commute T (f.gnsStarAlgHom a))

include hT in
lemma gns_commutant_coefficient (a b : A) :
    ⟪(f.toPreGNS a : f.GNS),T (f.toPreGNS b : f.GNS)⟫_ℂ =
      ⟪Pureness.stateGNSVector f,T (f.gnsStarAlgHom (star a*b) (Pureness.stateGNSVector f))⟫_ℂ := by
  rw [← Pureness.stateGNS_apply_vector f a,← Pureness.stateGNS_apply_vector f b]
  rw [← ContinuousLinearMap.adjoint_inner_right,map_mul,map_star,
    ContinuousLinearMap.star_eq_adjoint]
  change ⟪Pureness.stateGNSVector f,
    star (f.gnsStarAlgHom a) (T (f.gnsStarAlgHom b (Pureness.stateGNSVector f)))⟫_ℂ = _
  rw [← map_star]
  have he := congrArg (fun R : f.GNS →L[ℂ] f.GNS =>
    R (f.gnsStarAlgHom b (Pureness.stateGNSVector f))) (hT (star a)).eq
  change T (f.gnsStarAlgHom (star a) (f.gnsStarAlgHom b (Pureness.stateGNSVector f))) =
    f.gnsStarAlgHom (star a) (T (f.gnsStarAlgHom b (Pureness.stateGNSVector f))) at he
  rw [map_star,ContinuousLinearMap.star_eq_adjoint] at he
  rw [map_star,ContinuousLinearMap.star_eq_adjoint]
  exact congrArg (fun y => ⟪Pureness.stateGNSVector f,y⟫_ℂ) he.symm

include hT in
lemma spatial_coefficient_value {N : Type uN} [Fintype N] (k : N → K) (a : N → A) (x : A) :
    let ζ := algebraTensorVector f (∑ i, k i ⊗ₜ[ℂ] a i)
    ⟪ζ,spatialTensorOp (α x) T ζ⟫_ℂ =
      ⟪Pureness.stateGNSVector f,
        T (f.gnsStarAlgHom (coefficientMap α k a x) (Pureness.stateGNSVector f))⟫_ℂ := by
  classical
  dsimp only
  simp only [map_sum,algebraTensorVector_tmul,inner_sum,sum_inner]
  simp only [spatialTensorOp_coe,TensorProduct.mapL_tmul,UniformSpace.Completion.inner_coe,
    TensorProduct.inner_tmul]
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    sum_apply,smul_apply,inner_sum,inner_smul_right_eq_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gns_commutant_coefficient f T hT]

end CoefficientValue

end NuclearTrace

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

namespace NuclearTrace

section NuclearSeparation

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

theorem nuclear_coefficient_dual_bound (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (x : I → selfAdjoint A)
    (l : I → selfAdjoint A →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hl : ∀ i, ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l i a| ≤ C * (f a).re)
    (hsep : ∀ (n : ℕ) (k : Fin n → K) (a : Fin n → A),
      ∑ i, l i ⟨coefficientMap α k a (x i),coefficientMap_selfAdjoint α k a _ (x i).property⟩ ≤ 0) :
    ∑ i, l i (x i) ≤ 0 := by
  classical
  let : Module ℝ (SpatialHilbert K f.GNS →L[ℂ] SpatialHilbert K f.GNS) :=
    Module.complexToReal _
  have hrep (i : I) : ∃ T : f.GNS →L[ℂ] f.GNS, IsSelfAdjoint T ∧
      (∀ a, Commute T (f.gnsStarAlgHom a)) ∧
      ∀ a : selfAdjoint A, l i a =
        (⟪stateGNSVector f,T (f.gnsStarAlgHom a (stateGNSVector f))⟫_ℂ).re := by
    obtain ⟨T,hT,_,_,hcomm,hval⟩ := real_functional_in_commutant f (l i) C (hl i) hC
    exact ⟨T,hT,hcomm,hval⟩
  choose T hTsa hTcomm hTval using hrep
  let B := StarSubalgebra.centralizer ℂ (Set.range f.gnsStarAlgHom)
  let _ : IsClosed (B : Set (f.GNS →L[ℂ] f.GNS)) := Set.isClosed_centralizer _
  let _ : CStarAlgebra B := StarSubalgebra.cstarAlgebra B
  let ρ : B →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) := B.subtype
  have hρ (a : A) (b : B) : Commute (f.gnsStarAlgHom a) (ρ b) := by
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp b.property _ ⟨a,rfl⟩).1
  have hTB (i : I) : T i ∈ B := by
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨a,rfl⟩
    refine ⟨(hTcomm i a).symm.eq,?_⟩
    simpa only [map_star] using (hTcomm i (star a)).symm.eq
  let Ti (i : I) : B := ⟨T i,hTB i⟩
  let j := spatialStarTensorHom α ρ
  have hj : Function.Injective j := spatialStarTensorHom_injective_of_faithful α ρ hα
    Subtype.val_injective
  let _ : CStarAlgebra (SpatialHilbert K f.GNS →L[ℂ] SpatialHilbert K f.GNS) := inferInstance
  obtain ⟨σ,_,hσ⟩ := nuclear_cyclic_extension hA f.gnsStarAlgHom ρ hρ
    (stateGNSVector f) (stateGNSVector_norm f hf) j hj
  let S : SpatialHilbert K f.GNS →L[ℂ] SpatialHilbert K f.GNS :=
    ∑ i, spatialTensorOp (α (x i)) (T i)
  have hSsa : IsSelfAdjoint S := by
    apply isSelfAdjoint_sum
    intro i _
    change star (spatialTensorOp (α (x i)) (T i)) = _
    rw [← spatialTensorOp_star,(hTsa i).star_eq,← map_star,(x i).property.star_eq]
  have hquadDense (z : K ⊗[ℂ] A) :
      (⟪algebraTensorVector f z,S (algebraTensorVector f z)⟫_ℂ).re ≤ 0 := by
    obtain ⟨n,k,a,rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    have he (i : I) := spatial_coefficient_value α f (T i) (hTcomm i) k a (x i)
    change (⟪algebraTensorVector f (∑ j, k j ⊗ₜ[ℂ] a j),
      (∑ i, spatialTensorOp (α (x i)) (T i))
        (algebraTensorVector f (∑ j, k j ⊗ₜ[ℂ] a j))⟫_ℂ).re ≤ 0
    simp only [sum_apply,inner_sum,Complex.re_sum,he]
    have hv (i : I) := (hTval i ⟨coefficientMap α k a (x i),
      coefficientMap_selfAdjoint α k a _ (x i).property⟩).symm
    dsimp only at hv
    simp only [hv]
    exact hsep n k a
  have hquad (ζ : SpatialHilbert K f.GNS) : (⟪ζ,S ζ⟫_ℂ).re ≤ 0 := by
    exact (algebraTensorVector_dense (K := K) f).induction_on ζ
      (isClosed_le (show Continuous (fun ζ : SpatialHilbert K f.GNS =>
        (⟪ζ,S ζ⟫_ℂ).re) by fun_prop) continuous_const) hquadDense
  have hSle : S ≤ 0 := by
    simpa only [zero_smul] using operator_le_of_unit_quadratic hSsa
      (c := 0) (fun ζ _ => hquad ζ)
  have heval (i : I) : (σ (spatialTensorOp (α (x i)) (T i))).re = l i (x i) := by
    have he := hσ (x i : A) (Ti i)
    change σ (spatialStarTensorHom α ρ ((x i : A) ⊗ₜ[ℂ] Ti i)) = _ at he
    rw [spatialStarTensorHom_tmul] at he
    have hcomm := congrArg (fun R : f.GNS →L[ℂ] f.GNS => R (stateGNSVector f))
      (hTcomm i (x i)).eq
    exact (congrArg Complex.re
      (he.trans (congrArg (fun y => ⟪stateGNSVector f,y⟫_ℂ) hcomm.symm))).trans
      (hTval i (x i)).symm
  have hh := (σ.monotone hSle).1
  change (σ S).re ≤ (σ 0).re at hh
  simpa only [S,map_sum,Complex.re_sum,heval,map_zero,Complex.zero_re] using hh

end NuclearSeparation

end NuclearTrace

noncomputable section

open scoped Pointwise

namespace NuclearTrace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma linear_bound_of_seminorm_ball (p : Seminorm ℝ E) (f : E →L[ℝ] ℝ)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (h : ∀ y, p y < ε → |f y| < b) :
    ∀ y, |f y| ≤ (2*b/ε) * p y := by
  intro y
  by_cases hz : p y = 0
  · have hfy : f y = 0 := by
      by_contra hne
      have ha : 0 < |f y| := abs_pos.mpr hne
      let t := (b+1) / |f y|
      have ht : 0 < t := div_pos (by linarith) ha
      have hy : p (t • y) < ε := by
        rw [map_smul_eq_mul,hz,mul_zero]
        exact hε
      have hh := h (t • y) hy
      rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos ht] at hh
      have he : t * |f y| = b+1 := div_mul_cancel₀ (b+1) ha.ne'
      rw [he] at hh
      linarith
    simp [hfy,hz]
  · have hp : 0 < p y := lt_of_le_of_ne (apply_nonneg p y) (Ne.symm hz)
    let t := ε / (2*p y)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hp)
    have hy : p (t • y) < ε := by
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos ht]
      have he : t * p y = ε/2 := by dsimp [t]; field_simp
      rw [he]
      linarith
    have hh := h (t • y) hy
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos ht] at hh
    have he : b/t = (2*b/ε)*p y := by dsimp [t]; field_simp
    exact (lt_of_mul_lt_mul_left (show t * |f y| < t * ((2*b/ε)*p y) by
      rw [← he,mul_div_cancel₀ _ ht.ne']; exact hh) ht.le).le

theorem seminorm_cone_approximation_of_dual (p : Seminorm ℝ E) (hp : Continuous p)
    (S : Set E) (hS : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hsmul : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ S, t • s ∈ S) (x : E)
    (hx : ∀ f : E →L[ℝ] ℝ, (∃ C : ℝ, 0 ≤ C ∧ ∀ y, |f y| ≤ C * p y) →
      (∀ s ∈ S, f s ≤ 0) → f x ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, p (x-s) < ε := by
  classical
  by_contra hn
  let U : Set E := S + p.ball 0 ε
  have hU : Convex ℝ U := hS.add (p.convex_ball 0 ε)
  have hUopen : IsOpen U := by
    dsimp [U]
    rw [p.ball_zero_eq]
    exact (hp.isOpen_preimage _ isOpen_Iio).add_left
  have hxU : x ∉ U := by
    rintro ⟨s,hs,y,hy,hxy⟩
    apply hn
    refine ⟨s,hs,?_⟩
    have he : x-s = y := by change s + y = x at hxy; rw [← hxy]; abel
    simpa only [he,Seminorm.mem_ball_zero] using hy
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hU hUopen hxU
  have h0ball : (0 : E) ∈ p.ball 0 ε := by simpa using hε
  have h0U : (0 : E) ∈ U := ⟨0,h0,0,h0ball,by simp⟩
  have hfx : 0 < f x := by simpa only [map_zero] using hf 0 h0U
  have hbound : ∀ y, p y < ε → |f y| < f x := by
    intro y hy
    have hyU : y ∈ U := ⟨0,h0,y,by simpa using hy,by simp⟩
    have hnU : -y ∈ U := ⟨0,h0,-y,by simpa using hy,by simp⟩
    have hpos := hf y hyU
    have hneg := hf (-y) hnU
    rw [map_neg] at hneg
    exact abs_lt.mpr ⟨by linarith,hpos⟩
  have hcone : ∀ s ∈ S, f s ≤ 0 := by
    intro s hs
    by_contra hnp
    have hfs : 0 < f s := lt_of_not_ge hnp
    let t := (f x+1) / f s
    have ht : 0 < t := div_pos (by linarith) hfs
    have hts : t • s ∈ U := ⟨t • s,hsmul t ht.le s hs,0,h0ball,by simp⟩
    have htfx := hf (t • s) hts
    rw [map_smul,smul_eq_mul] at htfx
    have he : t * f s = f x+1 := div_mul_cancel₀ (f x+1) hfs.ne'
    rw [he] at htfx
    linarith
  have hnfx := hx f ⟨2*f x/ε,by positivity,
    linear_bound_of_seminorm_ball p f hε hfx hbound⟩ hcone
  exact (not_le_of_gt hfx) hnfx

end NuclearTrace

noncomputable section

open scoped ComplexOrder

namespace CurrentMain

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma traceOneNorm_le_norm (τ : Pureness.TracialState A) (a : A) :
    traceOneNorm τ a ≤ ‖a‖ := by
  exact (Complex.re_le_norm _).trans ((trace_norm_le_norm τ _).trans_eq CFC.norm_abs)

lemma tracialOneSeminorm_continuous (τ : Pureness.TracialState A) :
    Continuous (tracialOneSeminorm τ) := by
  apply Seminorm.continuous_of_le (p := tracialOneSeminorm τ)
    (q := normSeminorm ℝ (selfAdjoint A)) continuous_norm
  intro a
  exact traceOneNorm_le_norm τ a

lemma tracialOneSeminorm_of_nonneg (τ : Pureness.TracialState A) (a : selfAdjoint A)
    (ha : 0 ≤ (a : A)) : tracialOneSeminorm τ a = (τ.functional a).re := by
  simp [tracialOneSeminorm_apply,traceOneNorm,CFC.abs_of_nonneg (a : A) ha]

end CurrentMain

end

end

end

end

end

end

end

end

end

end

end

end

end

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
-- module Solutions.OAIQW_TracialSplitting.CoefficientApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

noncomputable section

open scoped Pointwise

noncomputable section

open scoped ComplexOrder

noncomputable section

open scoped ComplexOrder

namespace NuclearTrace

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

omit [PartialOrder A] [StarOrderedRing A] in
lemma coefficientCone_zero (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (0 : selfAdjoint A →ₗ[ℝ] selfAdjoint A) ∈ coefficientCone α := by
  apply ConvexCone.subset_hull
  refine ⟨0,Fin.elim0,Fin.elim0,?_⟩
  ext x
  simp [coefficientSelfAdjMap,coefficientMap]

lemma tracialTupleSeminorm_continuous (τ : Pureness.TracialState A) :
    Continuous (tracialTupleSeminorm (I := I) τ) := by
  simp only [funext (tracialTupleSeminorm_apply (I := I) τ)]
  apply continuous_finsetSum
  intro i _
  exact (CurrentMain.tracialOneSeminorm_continuous τ).comp (continuous_apply i)

lemma tracialTupleSeminorm_single [DecidableEq I] (τ : Pureness.TracialState A)
    (i : I) (a : selfAdjoint A) :
    tracialTupleSeminorm τ (Pi.single i a) = CurrentMain.tracialOneSeminorm τ a := by
  simp [tracialTupleSeminorm_apply,Pi.single_apply,apply_ite,CurrentMain.traceOneNorm]

theorem nuclear_tracial_coefficient_approximation (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (τ : Pureness.TracialState A) (x : I → selfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ coefficientCone α,
      ∑ i, CurrentMain.traceOneNorm τ ((x i : A) - L (x i)) < ε := by
  classical
  let C := (coefficientCone α).map (evalTuple x)
  have h0 : (0 : I → selfAdjoint A) ∈ C := by
    exact ⟨0,coefficientCone_zero α,by ext i; rfl⟩
  have hs : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ C, t • s ∈ C := by
    intro t ht s hs
    obtain rfl | ht := ht.eq_or_lt
    · simpa using h0
    · exact C.smul_mem ht hs
  have hdual (f : (I → selfAdjoint A) →L[ℝ] ℝ)
      (hf : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, |f y| ≤ c * tracialTupleSeminorm τ y)
      (hfc : ∀ s ∈ C, f s ≤ 0) : f x ≤ 0 := by
    obtain ⟨c,hc,hf⟩ := hf
    let l (i : I) : selfAdjoint A →ₗ[ℝ] ℝ :=
      f.toLinearMap.comp (LinearMap.single ℝ (fun _ : I => selfAdjoint A) i)
    have hl (i : I) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
        |l i a| ≤ c * (τ.functional a).re := by
      have hh := hf (Pi.single i a)
      rw [tracialTupleSeminorm_single,CurrentMain.tracialOneSeminorm_of_nonneg τ a ha] at hh
      exact hh
    have he (y : I → selfAdjoint A) : (∑ i, l i (y i)) = f y := by
      change (∑ i, f (Pi.single i (y i))) = f y
      rw [← map_sum]
      congr 1
      exact Finset.univ_sum_single y
    rw [← he x]
    apply nuclear_coefficient_dual_bound hA α hα τ.functional τ.normalized x l hc hl
    intro n k a
    rw [he]
    apply hfc
    refine ⟨coefficientSelfAdjMap α k a,?_,rfl⟩
    exact ConvexCone.subset_hull ⟨n,k,a,rfl⟩
  obtain ⟨s,hs,hclose⟩ := seminorm_cone_approximation_of_dual
    (tracialTupleSeminorm τ) (tracialTupleSeminorm_continuous τ)
    C C.convex h0 hs x hdual hε
  obtain ⟨L,hL,rfl⟩ := hs
  refine ⟨L,hL,?_⟩
  simpa only [tracialTupleSeminorm_apply,Pi.sub_apply,evalTuple,
    LinearMap.coe_mk,AddHom.coe_mk,(selfAdjoint A).coe_sub] using hclose

end NuclearTrace

noncomputable section

namespace NuclearTrace

open Set

variable {E : Type uE} {F : Type uF}

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

theorem compact_convex_uniform_cost {X : Set E} {Y : Set F}
    (hXne : X.Nonempty) (hX : IsCompact X) (hXconv : Convex ℝ X)
    (hYconv : Convex ℝ Y) (c : E → F → ℝ)
    (hcX : ∀ y ∈ Y, Continuous (fun x => c x y))
    (hcXconc : ∀ y ∈ Y, ConcaveOn ℝ X (fun x => c x y))
    (hcY : ∀ x ∈ X, ContinuousOn (c x) Y)
    (hcYconv : ∀ x ∈ X, ConvexOn ℝ Y (c x))
    {ε : ℝ} (hpoint : ∀ x ∈ X, ∃ y ∈ Y, c x y < ε) :
    ∃ y ∈ Y, ∀ x ∈ X, c x y < ε := by
  classical
  let U (y : Y) : Set E := {x | c x y < ε}
  have hUopen (y : Y) : IsOpen (U y) := (hcX y y.property).isOpen_preimage _ isOpen_Iio
  have hcover : X ⊆ ⋃ y : Y, U y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hpoint x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hxy⟩
  obtain ⟨s,hs⟩ := hX.elim_finite_subcover U hUopen hcover
  have hfinitePoint : ∀ x ∈ X, ∃ y ∈ Subtype.val '' (s : Set Y), -ε < -c x y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨y,⟨y,hy,rfl⟩,neg_lt_neg hxy⟩
  obtain ⟨y,hy,hyall⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite
    (f := fun x y => -c x y) hXne hX
    (fun y hy => (hcX y hy).neg.continuousOn.lowerSemicontinuousOn)
    (fun y hy => (hcXconc y hy).neg.quasiconvexOn)
    hYconv
    (fun x hx => (hcY x hx).neg.upperSemicontinuousOn)
    (fun x hx => (hcYconv x hx).neg.quasiconcaveOn)
    hXconv (s.finite_toSet.image Subtype.val)
    (fun _ hy => by obtain ⟨y,_,rfl⟩ := hy; exact y.property) hfinitePoint
  exact ⟨y,hy,fun x hx => neg_lt_neg_iff.mp (hyall x hx)⟩

end NuclearTrace

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

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
-- module Solutions.OAIQW_TracialSplitting.TraceNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

open scoped Pointwise

open scoped ComplexOrder

open scoped ComplexOrder

namespace Pureness

section

open scoped ComplexOrder

open Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma TracialState.norm_apply_le_four (τ : TracialState A) (a : A) :
    ‖τ.functional a‖ ≤ 4 * ‖a‖ := by
  obtain ⟨y, hypos, hynorm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg a
  nth_rw 1 [hy]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  calc
    _ ≤ ∑ i : Fin 4, ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hb := τ.functional.norm_apply_le_of_nonneg (y i) (hypos i)
      rw [τ.normalized, norm_one, one_mul] at hb
      exact hb.trans (hynorm i)
    _ = _ := by simp

omit [StarOrderedRing A] in
lemma isClosed_tracialStateCarrier : IsClosed (tracialStateCarrier (A := A)) := by
  have hnorm : IsClosed {f : WeakDual ℂ A | f 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have hpos : IsClosed {f : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ f a} := by
    have heq : {f : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ f a} =
        ⋂ a : A, ⋂ (_ : 0 ≤ a), {f : WeakDual ℂ A | 0 ≤ f a} := by
      ext f
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le continuous_const (WeakDual.eval_continuous a)
  have htrace : IsClosed {f : WeakDual ℂ A | ∀ a b, f (a * b) = f (b * a)} := by
    have heq : {f : WeakDual ℂ A | ∀ a b, f (a * b) = f (b * a)} =
        ⋂ a : A, ⋂ b : A, {f : WeakDual ℂ A | f (a * b) = f (b * a)} := by
      ext f
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (WeakDual.eval_continuous (a * b)) (WeakDual.eval_continuous (b * a))
  exact hnorm.inter (hpos.inter htrace)

lemma isCompact_tracialStateCarrier : IsCompact (tracialStateCarrier (A := A)) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 4).of_isClosed_subset
    isClosed_tracialStateCarrier
  intro f hf
  change f.toStrongDual ∈ Metric.closedBall 0 4
  rw [Metric.mem_closedBall, dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound f.toStrongDual (by norm_num)
  intro a
  exact (tracialStateFromWeakDual f hf).norm_apply_le_four a

end

open scoped ComplexOrder

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
lemma convex_tracialStateCarrier : Convex ℝ (tracialStateCarrier (A := A)) := by
  intro f hf g hg r s hr hs hrs
  refine ⟨?_,?_,?_⟩
  · change r • f 1 + s • g 1 = 1
    rw [hf.1,hg.1,← add_smul,hrs,one_smul]
  · intro a ha
    change 0 ≤ r • f a + s • g a
    exact add_nonneg (smul_nonneg hr (hf.2.1 a ha)) (smul_nonneg hs (hg.2.1 a ha))
  · intro a b
    change r • f (a*b) + s • g (a*b) = r • f (b*a) + s • g (b*a)
    rw [hf.2.2,hg.2.2]

end Pureness

namespace NuclearTrace

open scoped ComplexOrder

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

lemma traceTupleCost_continuous (x z : I → selfAdjoint A) :
    Continuous (traceTupleCost x z) := by
  apply continuous_finsetSum
  intro i _
  exact Complex.continuous_re.comp (WeakDual.eval_continuous _)

lemma traceTupleCost_eq (x z : I → selfAdjoint A) (τ : Pureness.TracialState A) :
    traceTupleCost x z τ.toWeakDual = tracialTupleSeminorm τ (x-z) := by
  rw [tracialTupleSeminorm_apply]
  rfl

lemma traceTupleCost_continuous_right (x : I → selfAdjoint A)
    (τ : Pureness.TracialState A) :
    Continuous (fun z => traceTupleCost x z τ.toWeakDual) := by
  simp only [traceTupleCost_eq]
  exact (tracialTupleSeminorm_continuous τ).comp (continuous_const.sub continuous_id)

lemma traceTupleCost_convex_right (x : I → selfAdjoint A)
    (τ : Pureness.TracialState A) {Y : Set (I → selfAdjoint A)} (hY : Convex ℝ Y) :
    ConvexOn ℝ Y (fun z => traceTupleCost x z τ.toWeakDual) := by
  refine ⟨hY,?_⟩
  intro y hy z hz r s hr hs hrs
  simp only [traceTupleCost_eq]
  have he : x - (r • y + s • z) = r • (x-y) + s • (x-z) := by
    rw [smul_sub,smul_sub]
    calc
      x - (r • y + s • z) = (r+s) • x - (r • y + s • z) := by rw [hrs,one_smul]
      _ = r • x - r • y + (s • x - s • z) := by rw [add_smul]; abel
  rw [he]
  exact (tracialTupleSeminorm τ).convexOn.2 (Set.mem_univ _) (Set.mem_univ _) hr hs hrs

theorem nuclear_uniform_tracial_coefficient_approximation
    (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (hT : Nonempty (Pureness.TracialState A)) (x : I → selfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ coefficientCone α, ∀ τ : Pureness.TracialState A,
      ∑ i, CurrentMain.traceOneNorm τ ((x i : A) - L (x i)) < ε := by
  classical
  let Y := (coefficientCone α).map (evalTuple x)
  let X := Pureness.tracialStateCarrier (A := A)
  have hXne : X.Nonempty := by
    obtain ⟨τ⟩ := hT
    exact ⟨τ.toWeakDual,τ.normalized,fun a ha => τ.functional.map_nonneg ha,τ.tracial⟩
  have hcost (τ : WeakDual ℂ A) (hτ : τ ∈ X) :
      (Pureness.tracialStateFromWeakDual τ hτ).toWeakDual = τ := by
    exact DFunLike.ext _ _ (fun _ => rfl)
  obtain ⟨z,hz,hall⟩ := @compact_convex_uniform_cost
    (WeakDual ℂ A) (I → selfAdjoint A) inferInstance inferInstance inferInstance
    inferInstance (WeakDual.instContinuousSMul ℝ) inferInstance inferInstance inferInstance
    inferInstance inferInstance X Y hXne
    Pureness.isCompact_tracialStateCarrier Pureness.convex_tracialStateCarrier
    Y.convex (fun τ z => traceTupleCost x z τ)
    (fun z _ => traceTupleCost_continuous x z)
    (fun z _ => (traceTupleCost x z).concaveOn Pureness.convex_tracialStateCarrier)
    (fun τ hτ => by
      rw [← hcost τ hτ]
      exact (traceTupleCost_continuous_right x _).continuousOn)
    (fun τ hτ => by
      rw [← hcost τ hτ]
      exact traceTupleCost_convex_right x _ Y.convex)
    (ε := ε) (by
      intro τ hτ
      obtain ⟨L,hL,hclose⟩ := nuclear_tracial_coefficient_approximation hA α hα
        (Pureness.tracialStateFromWeakDual τ hτ) x hε
      refine ⟨evalTuple x L,⟨L,hL,rfl⟩,?_⟩
      exact hclose)
  obtain ⟨L,hL,rfl⟩ := hz
  refine ⟨L,hL,fun τ => ?_⟩
  exact hall τ.toWeakDual ⟨τ.normalized,fun a ha => τ.functional.map_nonneg ha,τ.tracial⟩

end NuclearTrace

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.MatrixCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uJ uK uN


section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace NuclearTrace

section ChangeBasis

variable {A : Type uA} {K : Type uK} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))

variable {N : Type uN} {J : Type uJ} [Fintype N] [Fintype J]

lemma coefficientMap_change_vectors (k : N → K) (a : N → A)
    (e : J → K) (c : J → N → ℂ) (hk : ∀ i, k i = ∑ u, c u i • e u) (x : A) :
    coefficientMap α k a x = coefficientMap α e (fun u => ∑ i, c u i • a i) x := by
  classical
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,hk,map_sum,map_smul,
    inner_sum,sum_inner,inner_smul_left,inner_smul_right,star_sum,star_smul,
    Finset.mul_sum,Finset.sum_mul,Finset.smul_sum,Finset.sum_smul,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext u
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext u
    arg 2
    ext v
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change c v j * (star (c u i) * _) = _
  ring

lemma coefficientMap_orthonormal (k : N → K) (a : N → A) :
    ∃ (n : ℕ) (e : Fin n → K) (b : Fin n → A), Orthonormal ℂ e ∧
      coefficientMap α k a = coefficientMap α e b := by
  classical
  let S : Submodule ℂ K := Submodule.span ℂ (Set.range k)
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range k)
  let basis := stdOrthonormalBasis ℂ S
  let ki (i : N) : S := ⟨k i, Submodule.subset_span (Set.mem_range_self i)⟩
  let e (u : Fin (Module.finrank ℂ S)) : K := basis u
  let c (u : Fin (Module.finrank ℂ S)) (i : N) : ℂ := basis.repr (ki i) u
  have hk (i : N) : k i = ∑ u, c u i • e u := by
    have h := congrArg (fun z : S => (z : K)) (basis.sum_repr (ki i))
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using h.symm
  refine ⟨_,e,(fun u => ∑ i, c u i • a i),?_,?_⟩
  · exact S.subtypeₗᵢ.orthonormal_comp_iff.mpr basis.orthonormal
  · exact LinearMap.ext (fun x => coefficientMap_change_vectors α k a e c hk x)

end ChangeBasis

section Compression

variable {A : Type uA} {K : Type uK} {N : Type uN} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype N] [DecidableEq N]

lemma operatorMatrix_apply (T : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (i j : N) : operatorMatrix T i j =
      ⟪EuclideanSpace.basisFun N ℂ i,T (EuclideanSpace.basisFun N ℂ j)⟫_ℂ := by
  change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun N ℂ) T.toLinearMap) i j = _
  simp [LinearMap.toMatrixOrthonormal,LinearMap.toMatrix_apply,
    OrthonormalBasis.repr_apply_apply]

lemma compressionMatrix_apply (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) (x : A) (i j : N) :
    compressionMatrix α e he x i j = ⟪e i,α x (e j)⟫_ℂ := by
  change operatorMatrix _ i j = _
  rw [operatorMatrix_apply]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap,orthonormalInclusion_basis]

lemma compressionMatrix_one (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) : compressionMatrix α e he 1 = 1 := by
  ext i j
  rw [compressionMatrix_apply,map_one]
  exact orthonormal_iff_ite.mp he i j

lemma compressionMatrix_norm (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) (x : A) : ‖compressionMatrix α e he x‖ ≤ ‖x‖ := by
  let V := (orthonormalInclusion e he).toContinuousLinearMap
  have hV : ‖V‖ ≤ 1 := (orthonormalInclusion e he).norm_toContinuousLinearMap_le
  change ‖operatorMatrix ((V.adjoint.comp (α x)).comp V)‖ ≤ _
  apply (NonUnitalStarAlgHom.norm_apply_le
    ((operatorMatrix (N := N)).toStarAlgHom) _).trans
  calc
    ‖(V.adjoint.comp (α x)).comp V‖ ≤ ‖V.adjoint‖ * ‖α x‖ * ‖V‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖x‖ * 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le α x
    _ = ‖x‖ := by ring

lemma coefficientMap_factorization (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (e : N → K) (he : Orthonormal ℂ e) (a : N → A) (x : A) :
    coefficientMap α e a x =
      ∑ i, ∑ j, (compressionMatrix α e he x i j) • (star (a i)*a j) := by
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,compressionMatrix_apply]

end Compression

section Choi

variable {A : Type uA} {N : Type uN} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype N] [DecidableEq N]

lemma coefficient_choi_nonneg (a : N → A) :
    0 ≤ CStarMatrix.ofMatrix (fun i j : N => star (a i)*a j) := by
  classical
  by_cases hN : Nonempty N
  · let k : N := Classical.choice hN
    let R : CStarMatrix N N A := CStarMatrix.ofMatrix (fun i j => if i = k then a j else 0)
    have hr : star R*R = CStarMatrix.ofMatrix (fun i j : N => star (a i)*a j) := by
      ext i j
      rw [CStarMatrix.mul_apply]
      change (∑ l : N, star (if l = k then a i else 0) *
        (if l = k then a j else 0)) = star (a i)*a j
      simp
    rw [← hr]
    exact star_mul_self_nonneg R
  · have : IsEmpty N := not_nonempty_iff.mp hN
    have he : CStarMatrix.ofMatrix (fun i j : N => star (a i)*a j) = 0 := by
      ext i; exact isEmptyElim i
    rw [he]

end Choi

section FiniteSystems

variable {A : Type} [CStarAlgebra A]

attribute [instance] FiniteCoefficientSystem.finiteIndex FiniteCoefficientSystem.decidableIndex

section Synthesis

variable {I : Type} [Fintype I]

lemma matrixSynthesis_one [DecidableEq I] (a : I → A) :
    matrixSynthesis a 1 = ∑ i, star (a i)*a i := by
  change (∑ i, ∑ j, (1 : CStarMatrix I I ℂ) i j • (star (a i)*a j)) = _
  simp [CStarMatrix.one_apply]

end Synthesis

end FiniteSystems

section HullRepresentation

variable {A K : Type} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem coefficientCone_finite_system (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : selfAdjoint A →ₗ[ℝ] selfAdjoint A) (hL : L ∈ coefficientCone α) :
    ∃ F : FiniteCoefficientSystem A, ∀ x : selfAdjoint A, (L x : A) = F.output x := by
  apply (ConvexCone.hull_min (C := finiteSystemCone) ?_) hL
  rintro M ⟨n,k,a,rfl⟩
  obtain ⟨m,e,b,he,hmap⟩ := coefficientMap_orthonormal α k a
  let F : FiniteCoefficientSystem A := {
    Index := Fin m
    finiteIndex := inferInstance
    decidableIndex := inferInstance
    input := compressionMatrix α e he
    input_one := compressionMatrix_one α e he
    input_norm := compressionMatrix_norm α e he
    coefficient := b }
  refine ⟨F,fun x => ?_⟩
  change coefficientMap α k a (x : A) = matrixSynthesis b (compressionMatrix α e he (x : A))
  rw [hmap,coefficientMap_factorization α e he b]
  rfl

end HullRepresentation

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PartitionCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uD uI uJ uN uO

namespace CurrentMain

section

open Pureness

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceOneNorm_covariance_l2 (τ : TracialState D) (a b : D) :
    traceOneNorm τ (b * star b - a * star a) ≤
      (traceTwoNorm τ a + traceTwoNorm τ b) * traceTwoNorm τ (b-a) := by
  apply traceOneNorm_le_of_pairing τ ((selfAdjoint_covariance b).sub
    (selfAdjoint_covariance a))
  intro s _ hs
  have he : b * star b - a * star a =
      (b-a) * star b + a * star (b-a) := by
    rw [star_sub]
    noncomm_ring
  rw [he,mul_add,map_add,Complex.add_re]
  have hsbound (v : D) : traceTwoNorm τ (s*v) ≤ traceTwoNorm τ v := by
    exact (traceTwoNorm_mul_left τ s v).trans
      ((mul_le_mul_of_nonneg_right hs (traceTwoNorm_nonneg τ v)).trans_eq (one_mul _))
  have hfirst : (τ.functional (s*((b-a)*star b))).re ≤
      traceTwoNorm τ (b-a) * traceTwoNorm τ b := by
    apply (Complex.re_le_norm _).trans
    rw [← mul_assoc]
    exact (trace_norm_mul_le τ _ _).trans (by
      rw [traceTwoNorm_star]
      exact mul_le_mul_of_nonneg_right (hsbound _) (traceTwoNorm_nonneg τ _))
  have hsecond : (τ.functional (s*(a*star (b-a)))).re ≤
      traceTwoNorm τ a * traceTwoNorm τ (b-a) := by
    apply (Complex.re_le_norm _).trans
    rw [← mul_assoc]
    exact (trace_norm_mul_le τ _ _).trans (by
      rw [traceTwoNorm_star]
      exact mul_le_mul_of_nonneg_right (hsbound _) (traceTwoNorm_nonneg τ _))
  nlinarith

variable {I : Type uI} [Fintype I]

lemma traceOneNorm_covariance_sum_l2 (τ : TracialState D) (a b : I → D) :
    traceOneNorm τ ((∑ i, b i * star (b i)) - (∑ i, a i * star (a i))) ^ 2 ≤
      2 * ((∑ i, traceTwoNorm τ (a i)^2) + (∑ i, traceTwoNorm τ (b i)^2)) *
        (∑ i, traceTwoNorm τ (b i-a i)^2) := by
  classical
  let f (i : I) := (traceTwoNorm τ (a i) + traceTwoNorm τ (b i)) *
    traceTwoNorm τ (b i-a i)
  have hf : ∀ i, 0 ≤ f i := fun i => mul_nonneg
    (add_nonneg (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _))
    (traceTwoNorm_nonneg τ _)
  have hle : traceOneNorm τ ((∑ i, b i * star (b i)) - (∑ i, a i * star (a i))) ≤
      ∑ i, f i := by
    rw [← Finset.sum_sub_distrib]
    exact (traceOneNorm_sum_le τ _ (fun i =>
      (selfAdjoint_covariance _).sub (selfAdjoint_covariance _))).trans
      (Finset.sum_le_sum fun i _ => traceOneNorm_covariance_l2 τ (a i) (b i))
  have hCS : (∑ i, f i)^2 ≤
      (∑ i, 2 * (traceTwoNorm τ (a i)^2 + traceTwoNorm τ (b i)^2)) *
        (∑ i, traceTwoNorm τ (b i-a i)^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; positivity
    · intro i _; positivity
    · intro i _
      dsimp [f]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [sq_nonneg (traceTwoNorm τ (a i)-traceTwoNorm τ (b i))]
  apply (sq_le_sq₀ (traceOneNorm_nonneg τ _) (Finset.sum_nonneg fun i _ => hf i)).mpr
    hle |>.trans
  simpa only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc] using hCS

lemma global_partition_covariance_l2 {J : Type uJ} [Fintype J]
    (τ : TracialState D) (q : J → D) (hq : ∀ j, IsStarProjection (q j))
    (hsum : ∑ j, q j = 1) (a b : I → D) :
    (∑ j, traceOneNorm τ ((∑ i, star (b i) * q j * b i) -
      ∑ i, star (a i) * q j * a i)) ^ 2 ≤
      2 * ((∑ i, traceTwoNorm τ (a i)^2) + (∑ i, traceTwoNorm τ (b i)^2)) *
        (∑ i, traceTwoNorm τ (b i-a i)^2) := by
  classical
  let c (j : J) (i : I) := star (a i)*q j
  let d (j : J) (i : I) := star (b i)*q j
  have hc (j : J) (i : I) : c j i * star (c j i) = star (a i)*q j*a i := by
    dsimp [c]
    rw [star_mul,star_star,(hq j).isSelfAdjoint.star_eq]
    simp only [mul_assoc,← mul_assoc (q j) (q j) (a i),(hq j).isIdempotentElem.eq]
  have hd (j : J) (i : I) : d j i * star (d j i) = star (b i)*q j*b i := by
    dsimp [d]
    rw [star_mul,star_star,(hq j).isSelfAdjoint.star_eq]
    simp only [mul_assoc,← mul_assoc (q j) (q j) (b i),(hq j).isIdempotentElem.eq]
  have he (j : J) :
      traceOneNorm τ ((∑ i, star (b i)*q j*b i) - ∑ i, star (a i)*q j*a i)^2 ≤
      (2 * ((∑ i, traceTwoNorm τ (c j i)^2) + ∑ i, traceTwoNorm τ (d j i)^2)) *
        (∑ i, traceTwoNorm τ (d j i-c j i)^2) := by
    simpa only [hc,hd,← mul_assoc] using traceOneNorm_covariance_sum_l2 τ (c j) (d j)
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun j => traceOneNorm τ ((∑ i, star (b i)*q j*b i) - ∑ i, star (a i)*q j*a i))
    (f := fun j => 2*((∑ i, traceTwoNorm τ (c j i)^2)+∑ i, traceTwoNorm τ (d j i)^2))
    (g := fun j => ∑ i, traceTwoNorm τ (d j i-c j i)^2)
    (fun j _ => by positivity) (fun j _ => by positivity) (fun j _ => he j)
  have hca : (∑ j, ∑ i, traceTwoNorm τ (c j i)^2) = ∑ i, traceTwoNorm τ (a i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [c,traceTwoNorm_star] using traceTwoNorm_sq_partition_right τ q hq hsum (star (a i))
  have hdb : (∑ j, ∑ i, traceTwoNorm τ (d j i)^2) = ∑ i, traceTwoNorm τ (b i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [d,traceTwoNorm_star] using traceTwoNorm_sq_partition_right τ q hq hsum (star (b i))
  have hdc : (∑ j, ∑ i, traceTwoNorm τ (d j i-c j i)^2) =
      ∑ i, traceTwoNorm τ (b i-a i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c,d,← sub_mul,← star_sub]
    rw [traceTwoNorm_sq_partition_right τ q hq hsum,traceTwoNorm_star]
  have hf : (∑ j, 2*((∑ i, traceTwoNorm τ (c j i)^2)+∑ i, traceTwoNorm τ (d j i)^2)) =
      2*((∑ i, traceTwoNorm τ (a i)^2)+∑ i, traceTwoNorm τ (b i)^2) := by
    rw [← Finset.mul_sum,Finset.sum_add_distrib,hca,hdb]
  simpa only [hf,hdc] using hCS

end

section

open scoped ComplexOrder

section ChoiKraus

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

lemma choi_sqrt_factorization (Q : CStarMatrix N N D) (hQ : 0 ≤ Q) :
    ∃ V : CStarMatrix N N D, IsSelfAdjoint V ∧ star V * V = Q := by
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (CStarMatrix N N D) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix N N D) :=
    CStarAlgebra.instNonnegSpectrumClass
  refine ⟨CFC.sqrt Q, (CFC.sqrt_nonneg Q).isSelfAdjoint, ?_⟩
  rw [((CFC.sqrt_nonneg Q).isSelfAdjoint : IsSelfAdjoint (CFC.sqrt Q)).star_eq]
  exact CFC.sqrt_mul_sqrt_self Q hQ

lemma choi_bistochastic_family (Q : CStarMatrix N N D) (hQ : 0 ≤ Q)
    (hmass : ∑ i, Q i i = 1) :
    ∃ a : (N × N) → D,
      (∑ i, star (a i) * a i = 1) ∧
      (∑ i, a i * star (a i) = 1) ∧
      ∀ i j, Q i j = ∑ k, star (a (k,i)) * a (k,j) := by
  classical
  obtain ⟨V,hV,hVV⟩ := choi_sqrt_factorization Q hQ
  have hentry (i j : N) : Q i j = ∑ k, star (V k i) * V k j := by
    rw [← hVV]
    simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply]
  refine ⟨fun i => V i.1 i.2, ?_, ?_, hentry⟩
  · rw [Fintype.sum_prod_type,Finset.sum_comm]
    simpa only [← hentry] using hmass
  · rw [Fintype.sum_prod_type]
    have hstar (i j : N) : star (V i j) = V j i :=
      CStarMatrix.star_apply_of_isSelfAdjoint hV
    simp_rw [hstar]
    have hsum (i : N) : (∑ j, V i j * V j i) = Q i i := by
      rw [hentry]
      simp only [hstar]
    simpa only [hsum] using hmass

open scoped CStarAlgebra

lemma sum_scalarMatrixUnit_diag : (∑ i : N, scalarMatrixUnit i i) = 1 := by
  ext i j
  change (∑ k : N, Matrix.single k k (1 : ℂ)) i j = if i = j then 1 else 0
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

lemma scalarMatrixUnit_expansion (T : CStarMatrix N N ℂ) :
    (∑ i, ∑ j, T i j • scalarMatrixUnit i j) = T := by
  apply CStarMatrix.ext
  intro k l
  change (∑ i, ∑ j, T i j • Matrix.single i j (1 : ℂ)) k l = T k l
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
  simp [ite_and]

omit [PartialOrder D] [StarOrderedRing D] in
lemma linearMap_choi_expansion (φ : CStarMatrix N N ℂ →ₗ[ℂ] D)
    (T : CStarMatrix N N ℂ) :
    φ T = ∑ i, ∑ j, T i j • φ (scalarMatrixUnit i j) := by
  conv_lhs => rw [← scalarMatrixUnit_expansion T]
  simp only [map_sum,map_smul]

lemma scalar_contraction_dilation (T : CStarMatrix N N ℂ) (hT : ‖T‖ ≤ 1) :
    ∃ S : CStarMatrix N N ℂ, star T * T + star S * S = 1 := by
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (CStarMatrix N N ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix N N ℂ) :=
    CStarAlgebra.instNonnegSpectrumClass
  have hTT : star T*T ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star T*T) (star_mul_self_nonneg T)).mp
    calc
      ‖star T*T‖ = ‖T‖*‖T‖ := CStarRing.norm_star_mul_self (x := T)
      _ ≤ 1 := by nlinarith [norm_nonneg T]
  obtain ⟨S,_,hS⟩ := choi_sqrt_factorization (1-star T*T) (sub_nonneg.mpr hTT)
  exact ⟨S,by rw [hS]; abel⟩

end ChoiKraus

section ScalarMix

variable {D : Type uD} [CStarAlgebra D]

variable {I : Type uI} {O : Type uO} [Fintype I] [Fintype O] [DecidableEq I]

omit [DecidableEq I] in
lemma scalarMix_covariance (R : Matrix O I ℂ) (a : I → D) (q : D) :
    (∑ o, star (scalarMix R a o) * q * scalarMix R a o) =
      ∑ i, ∑ j, (∑ o, star (R o i) * R o j) • (star (a i)*q*a j) := by
  classical
  have he (o : O) : star (scalarMix R a o)*q*scalarMix R a o =
      ∑ i, ∑ j, (star (R o i)*R o j) • (star (a i)*q*a j) := by
    simp only [scalarMix,star_sum,star_smul,Finset.sum_mul,Finset.mul_sum,
      smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  simp_rw [he,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma scalarMix_dilation_covariance {N : Type uN} [Fintype N] [DecidableEq N]
    (T S : CStarMatrix N N ℂ) (hTS : star T*T + star S*S = 1)
    (a : N → D) (q : D) :
    (∑ i, star (scalarMix (CStarMatrix.ofMatrix.symm T) a i)*q*scalarMix (CStarMatrix.ofMatrix.symm T) a i) +
      (∑ i, star (scalarMix (CStarMatrix.ofMatrix.symm S) a i)*q*scalarMix (CStarMatrix.ofMatrix.symm S) a i) =
        ∑ i, star (a i)*q*a i := by
  classical
  have hentry (i j : N) :
      (∑ k, star (T k i)*T k j) + (∑ k, star (S k i)*S k j) =
      if i=j then 1 else 0 := by
    have h := congrArg (fun M : CStarMatrix N N ℂ => M i j) hTS
    simpa only [CStarMatrix.add_apply,CStarMatrix.mul_apply,CStarMatrix.star_apply,
      CStarMatrix.one_apply] using h
  rw [scalarMix_covariance,scalarMix_covariance,← Finset.sum_add_distrib]
  simp only [CStarMatrix.ofMatrix_symm_apply]
  simp_rw [← Finset.sum_add_distrib,← add_smul,hentry,ite_smul,one_smul,zero_smul]
  simp

end ScalarMix

variable {D : Type uD} [CStarAlgebra D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

lemma choi_evaluation (φ : CStarMatrix N N ℂ →ₗ[ℂ] D) (a : (N × N) → D)
    (ha : ∀ i j, φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i))*a (k,j))
    (T : CStarMatrix N N ℂ) :
    φ T = ∑ k, ∑ i, star (a (k,i))*scalarMix (CStarMatrix.ofMatrix.symm T) (fun j => a (k,j)) i := by
  rw [linearMap_choi_expansion]
  simp only [ha,Finset.smul_sum,scalarMix,Finset.mul_sum,mul_smul_comm,
    CStarMatrix.ofMatrix_symm_apply]
  trans ∑ i, ∑ k, ∑ j, T i j • (star (a (k,i))*a (k,j))
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

end

open Pureness

open scoped ComplexOrder CStarAlgebra

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

omit [PartialOrder D] [StarOrderedRing D] in
lemma choi_coupling (φ : CStarMatrix N N ℂ →ₗ[ℂ] D) (a : (N × N) → D)
    (ha : ∀ i j, φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i))*a (k,j))
    (ha1 : ∑ i, star (a i)*a i = 1)
    (T : CStarMatrix N N ℂ) (hT : ‖T‖ ≤ 1) (x : unitary D) :
    ∃ b v : ((N × N) ⊕ (N × N)) → D,
      (∀ q, (∑ i, star (b i)*q*b i) = ∑ i, star (a i)*q*a i) ∧
      (∀ q, (∑ i, star (v i)*q*v i) =
        star (x : D)*(∑ i, star (a i)*q*a i)*(x : D)) ∧
      (∑ i, star (b i)*b i = 1) ∧ (∑ i, star (v i)*v i = 1) ∧
      (∑ i, star (b i-v i)*(b i-v i)) =
        2 - star (φ T)*(x : D) - star (x : D)*φ T := by
  classical
  obtain ⟨S,hTS⟩ := scalar_contraction_dilation T hT
  let b : ((N × N) ⊕ (N × N)) → D := Sum.elim
    (fun z => scalarMix (CStarMatrix.ofMatrix.symm T) (fun j => a (z.1,j)) z.2)
    (fun z => scalarMix (CStarMatrix.ofMatrix.symm S) (fun j => a (z.1,j)) z.2)
  let v : ((N × N) ⊕ (N × N)) → D := Sum.elim (fun z => a z*(x : D)) (fun _ => 0)
  have hb (q : D) : (∑ i, star (b i)*q*b i) = ∑ i, star (a i)*q*a i := by
    simp only [b,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => scalarMix_dilation_covariance T S hTS
      (fun i => a (k,i)) q)
  have hv (q : D) : (∑ i, star (v i)*q*v i) =
      star (x : D)*(∑ i, star (a i)*q*a i)*(x : D) := by
    simp only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,star_zero,zero_mul,
      Finset.sum_const_zero,add_zero,star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  have hb1 : (∑ i, star (b i)*b i) = 1 := by
    simpa only [mul_one] using (hb 1).trans (by simpa only [mul_one] using ha1)
  have hv1 : (∑ i, star (v i)*v i) = 1 := by
    simpa only [mul_one,ha1,Unitary.coe_star_mul_self] using hv 1
  have hcross : (∑ i, star (v i)*b i) = star (x : D)*φ T := by
    rw [choi_evaluation φ a ha T]
    simp only [v,b,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,star_zero,zero_mul,
      Finset.sum_const_zero,add_zero,star_mul,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hcross' : (∑ i, star (b i)*v i) = star (φ T)*(x : D) := by
    have h := congrArg star hcross
    simpa only [star_sum,star_mul,star_star] using h
  refine ⟨b,v,hb,hv,hb1,hv1,?_⟩
  have he (i : ((N × N) ⊕ (N × N))) :
      star (b i-v i)*(b i-v i) =
        star (b i)*b i + star (v i)*v i - star (b i)*v i - star (v i)*b i := by
    rw [star_sub]
    noncomm_ring
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,hb1,hv1,hcross,hcross']
  norm_num

lemma trace_choi_coupling_pairing {I : Type uI} [Fintype I]
    (τ : TracialState D) (b v : I → D) (z : D) (x : unitary D)
    (herr : (∑ i, star (b i-v i)*(b i-v i)) =
      2 - star z*(x : D) - star (x : D)*z) :
    (∑ i, traceTwoNorm τ (b i-v i)^2) =
      2*(τ.functional (star (x : D)*((x : D)-z))).re := by
  let y : D := star (x : D)*((x : D)-z)
  have he : 2 - star z*(x : D) - star (x : D)*z = y+star y := by
    dsimp [y]
    simp only [star_mul,star_sub,star_star,mul_sub,Unitary.coe_star_mul_self,star_one]
    rw [show (2 : D) = 1+1 by norm_num]
    abel
  rw [show (∑ i, traceTwoNorm τ (b i-v i)^2) =
      (τ.functional (∑ i, star (b i-v i)*(b i-v i))).re by
        simp only [traceTwoNorm_sq,map_sum,Complex.re_sum],herr,he]
  simp only [map_add,map_star,Complex.add_re,Complex.star_def,Complex.conj_re]
  ring

lemma choi_global_partition_pairing {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (τ : TracialState D) (b v : I → D) (z : D) (x : unitary D)
    (hb : ∑ i, star (b i)*b i = 1) (hv : ∑ i, star (v i)*v i = 1)
    (herr : (∑ i, star (b i-v i)*(b i-v i)) =
      2 - star z*(x : D) - star (x : D)*z)
    (q : J → D) (hq : ∀ j, IsStarProjection (q j)) (hsum : ∑ j, q j = 1) :
    (∑ j, traceOneNorm τ ((∑ i, star (b i)*q j*b i) -
      ∑ i, star (v i)*q j*v i))^2 ≤
        8*(τ.functional (star (x : D)*((x : D)-z))).re := by
  have hs (c : I → D) (hc : ∑ i, star (c i)*c i = 1) :
      (∑ i, traceTwoNorm τ (c i)^2) = 1 := by
    simp only [traceTwoNorm_sq,← Complex.re_sum,← map_sum,hc,τ.normalized,Complex.one_re]
  have h := global_partition_covariance_l2 τ q hq hsum v b
  rw [hs b hb,hs v hv,trace_choi_coupling_pairing τ b v z x herr] at h
  nlinarith

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TraceConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA


section

noncomputable section

namespace NuclearTrace

open scoped ComplexOrder

lemma clipScalar_continuous : Continuous clipScalar := by
  apply Continuous.inv₀ (Real.continuous_sqrt.comp (continuous_id.max continuous_const))
  intro t
  exact ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (le_max_right t 1)))

lemma clipScalar_nonneg (t : ℝ) : 0 ≤ clipScalar t := by
  exact inv_nonneg.2 (Real.sqrt_nonneg _)

lemma clipScalar_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1-clipScalar t*t*clipScalar t ∧
    1-clipScalar t*t*clipScalar t ≤ |t-1| ∧
    (1-clipScalar t)*t*(1-clipScalar t) ≤ |t-1| := by
  by_cases h : t ≤ 1
  · simp only [clipScalar,max_eq_right h,Real.sqrt_one,inv_one,one_mul,mul_one,
      sub_self,zero_mul,mul_zero]
    rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact ⟨sub_nonneg.2 h, le_rfl, sub_nonneg.2 h⟩
  · have h1 : 1 ≤ t := le_of_not_ge h
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one h1
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hsq := Real.sq_sqrt ht
    have hs1 : 1 ≤ Real.sqrt t := (Real.le_sqrt zero_le_one ht).2 (by simpa using h1)
    have he : (Real.sqrt t)⁻¹*t*(Real.sqrt t)⁻¹ = 1 := by
      calc
        _ = (Real.sqrt t)⁻¹*(Real.sqrt t)^2*(Real.sqrt t)⁻¹ := by rw [hsq]
        _ = 1 := by field_simp [ne_of_gt hs0]
    simp only [clipScalar,max_eq_left h1,he,sub_self,abs_of_nonneg (sub_nonneg.2 h1)]
    refine ⟨le_rfl,sub_nonneg.2 h1,?_⟩
    have he' : (1-(Real.sqrt t)⁻¹)*t*(1-(Real.sqrt t)⁻¹) =
        (Real.sqrt t-1)^2 := by
      calc
        _ = (1-(Real.sqrt t)⁻¹)*(Real.sqrt t)^2*(1-(Real.sqrt t)⁻¹) := by rw [hsq]
        _ = _ := by field_simp [ne_of_gt hs0]
    rw [he']
    nlinarith

section Algebra

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma rowNormalizer_nonneg (b : A) : 0 ≤ rowNormalizer b :=
  cfc_nonneg (fun t _ => clipScalar_nonneg t)

lemma abs_sub_one_cfc {b : A} (hb : IsSelfAdjoint b) :
    CFC.abs (b-1) = cfc (fun t : ℝ => |t-1|) b := by
  rw [CFC.abs_eq_cfcₙ_norm (b-1) (hb.sub (IsSelfAdjoint.one A)),
    cfcₙ_eq_cfc (hf0 := norm_zero)]
  have he : cfc (fun t : ℝ => t-1) b = b-1 := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => 1) b, cfc_id' ℝ b hb,cfc_const_one ℝ b hb]
  rw [← he,← cfc_comp' (fun t : ℝ => ‖t‖) (fun t : ℝ => t-1) b]
  rfl

theorem rowNormalizer_bounds {b : A} (hb : 0 ≤ b) :
    0 ≤ 1-rowNormalizer b*b*rowNormalizer b ∧
    1-rowNormalizer b*b*rowNormalizer b ≤ CFC.abs (b-1) ∧
    (1-rowNormalizer b)*b*(1-rowNormalizer b) ≤ CFC.abs (b-1) := by
  have hs := hb.isSelfAdjoint
  have hf := clipScalar_continuous.continuousOn (s := spectrum ℝ b)
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ b) := continuousOn_id
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ b) := continuousOn_const
  have hprod : rowNormalizer b*b*rowNormalizer b =
      cfc (fun t : ℝ => clipScalar t*t*clipScalar t) b := by
    rw [cfc_mul (fun t : ℝ => clipScalar t*t) clipScalar b
      (show ContinuousOn (fun t : ℝ => clipScalar t*t) _ from hf.mul hid) hf,
      cfc_mul clipScalar (fun t : ℝ => t) b hf hid,cfc_id' ℝ b hs]
    rfl
  have hres : 1-rowNormalizer b*b*rowNormalizer b =
      cfc (fun t : ℝ => 1-clipScalar t*t*clipScalar t) b := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun t => clipScalar t*t*clipScalar t) b hone
      (show ContinuousOn (fun t : ℝ => clipScalar t*t*clipScalar t) _ from (hf.mul hid).mul hf),
      cfc_const_one ℝ b hs,hprod]
  have herr : (1-rowNormalizer b)*b*(1-rowNormalizer b) =
      cfc (fun t : ℝ => (1-clipScalar t)*t*(1-clipScalar t)) b := by
    rw [cfc_mul (fun t : ℝ => (1-clipScalar t)*t) (fun t => 1-clipScalar t) b
      (show ContinuousOn (fun t : ℝ => (1-clipScalar t)*t) _ from (hone.sub hf).mul hid)
      (show ContinuousOn (fun t : ℝ => 1-clipScalar t) _ from hone.sub hf),
      cfc_mul (fun t : ℝ => 1-clipScalar t) (fun t => t) b
        (show ContinuousOn (fun t : ℝ => 1-clipScalar t) _ from hone.sub hf) hid,
      cfc_sub (fun _ : ℝ => 1) clipScalar b hone hf,
      cfc_id' ℝ b hs,cfc_const_one ℝ b hs]
    rfl
  rw [hres,herr,abs_sub_one_cfc hs]
  have hspec (t) (ht : t ∈ spectrum ℝ b) : 0 ≤ t :=
    (spectrum_nonneg_of_nonneg hb) ht
  refine ⟨cfc_nonneg (fun t ht => (clipScalar_bounds (hspec t ht)).1),?_,?_⟩
  · exact cfc_mono (fun t ht => (clipScalar_bounds (hspec t ht)).2.1)
      ((hone.sub ((hf.mul hid).mul hf))) (by fun_prop)
  · exact cfc_mono (fun t ht => (clipScalar_bounds (hspec t ht)).2.2)
      (((hone.sub hf).mul hid).mul (hone.sub hf)) (by fun_prop)

end Algebra

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.NuclearApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open scoped ComplexOrder

open CurrentMain Pureness

namespace NuclearTrace

section Normalization

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype I] [DecidableEq I]

lemma scalarMix_trace_sq_le (τ : TracialState A) (a : I → A)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) :
    (∑ i, traceTwoNorm τ (scalarMix (CStarMatrix.ofMatrix.symm T) a i)^2) ≤
      ∑ i, traceTwoNorm τ (a i)^2 := by
  obtain ⟨S,hS⟩ := scalar_contraction_dilation T hT
  have h := scalarMix_dilation_covariance T S hS a 1
  have ht := congrArg (fun x : A => (τ.functional x).re) h
  simp only [mul_one,map_add,map_sum,Complex.add_re,Complex.re_sum,
    ← traceTwoNorm_sq] at ht
  have hn : 0 ≤ ∑ i, traceTwoNorm τ (scalarMix (CStarMatrix.ofMatrix.symm S) a i)^2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

omit [PartialOrder A] [StarOrderedRing A] [DecidableEq I] in
lemma matrixSynthesis_eq_mix (a : I → A) (T : CStarMatrix I I ℂ) :
    matrixSynthesis a T = ∑ i, star (a i)*scalarMix (CStarMatrix.ofMatrix.symm T) a i := by
  change (∑ i, ∑ j, T i j • (star (a i)*a j)) = _
  simp only [scalarMix,Finset.mul_sum,mul_smul_comm,CStarMatrix.ofMatrix_symm_apply]

omit [PartialOrder A] [StarOrderedRing A] [DecidableEq I] in
lemma scalarMix_sub (T : CStarMatrix I I ℂ) (a b : I → A) (i : I) :
    scalarMix (CStarMatrix.ofMatrix.symm T) (fun j => a j-b j) i =
      scalarMix (CStarMatrix.ofMatrix.symm T) a i -
      scalarMix (CStarMatrix.ofMatrix.symm T) b i := by
  simp only [scalarMix,smul_sub,Finset.sum_sub_distrib]

omit [DecidableEq I] in
lemma trace_pairing_sum_bound (τ : TracialState A) (u : A) (hu : ‖u‖ ≤ 1)
    (a b : I → A) :
    ‖τ.functional (u*(∑ i, star (a i)*b i))‖^2 ≤
      (∑ i, traceTwoNorm τ (a i)^2)*(∑ i, traceTwoNorm τ (b i)^2) := by
  have hb (i : I) : ‖τ.functional (u*(star (a i)*b i))‖ ≤
      traceTwoNorm τ (a i)*traceTwoNorm τ (b i) := by
    rw [← mul_assoc]
    exact (trace_norm_mul_le τ _ _).trans (by
      apply mul_le_mul_of_nonneg_right _ (traceTwoNorm_nonneg τ _)
      exact (traceTwoNorm_mul_left τ _ _).trans (by
        rw [traceTwoNorm_star]
        exact (mul_le_mul_of_nonneg_right hu (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _)))
  have he : ‖τ.functional (u*(∑ i, star (a i)*b i))‖ ≤
      ∑ i, traceTwoNorm τ (a i)*traceTwoNorm τ (b i) := by
    rw [Finset.mul_sum,map_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb i)
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _))).mpr he |>.trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact sq_nonneg _
  · intro i _; exact sq_nonneg _
  · intro i _; rw [mul_pow]

lemma matrixSynthesis_difference_pairing (τ : TracialState A) (a b : I → A)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) (u : A) (hu : ‖u‖ ≤ 1) :
    ‖τ.functional (u*(matrixSynthesis a T-matrixSynthesis b T))‖^2 ≤
      2*((∑ i, traceTwoNorm τ (a i)^2)+(∑ i, traceTwoNorm τ (b i)^2))*
        (∑ i, traceTwoNorm τ (a i-b i)^2) := by
  let d : I → A := fun i => a i-b i
  let ma := scalarMix (CStarMatrix.ofMatrix.symm T) a
  let md := scalarMix (CStarMatrix.ofMatrix.symm T) d
  have he : matrixSynthesis a T-matrixSynthesis b T =
      (∑ i, star (d i)*ma i)+(∑ i, star (b i)*md i) := by
    rw [matrixSynthesis_eq_mix,matrixSynthesis_eq_mix,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [d,ma,md]
    rw [scalarMix_sub,star_sub]
    noncomm_ring
  have h1 := trace_pairing_sum_bound τ u hu d ma
  have h2 := trace_pairing_sum_bound τ u hu b md
  have hm1 := scalarMix_trace_sq_le τ a T hT
  have hm2 := scalarMix_trace_sq_le τ d T hT
  have hd0 : 0 ≤ ∑ i, traceTwoNorm τ (d i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ i, traceTwoNorm τ (b i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb1 := h1.trans (mul_le_mul_of_nonneg_left hm1 hd0)
  have hb2 := h2.trans (mul_le_mul_of_nonneg_left hm2 hb0)
  rw [he,mul_add,map_add]
  have hn := norm_add_le (τ.functional (u*∑ i, star (d i)*ma i))
    (τ.functional (u*∑ i, star (b i)*md i))
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  dsimp [d] at hb1 hb2
  nlinarith [sq_nonneg (‖τ.functional (u*∑ i, star (d i)*ma i)‖-
    ‖τ.functional (u*∑ i, star (b i)*md i)‖)]

omit [DecidableEq I] in
lemma row_mass_nonneg (a : I → A) : 0 ≤ ∑ i, star (a i)*a i :=
  Finset.sum_nonneg fun i _ => star_mul_self_nonneg (a i)

omit [DecidableEq I] in
lemma rowNormalizer_mass (a : I → A) :
    (∑ i, star (a i*rowNormalizer (∑ j, star (a j)*a j)) *
      (a i*rowNormalizer (∑ j, star (a j)*a j))) =
    rowNormalizer (∑ j, star (a j)*a j)*(∑ j, star (a j)*a j)*
      rowNormalizer (∑ j, star (a j)*a j) := by
  have hs := (rowNormalizer_nonneg (∑ j, star (a j)*a j)).isSelfAdjoint.star_eq
  simp only [star_mul,hs,Finset.mul_sum,Finset.sum_mul,mul_assoc]

omit [DecidableEq I] in
lemma rowNormalizer_error_mass (a : I → A) :
    (∑ i, star (a i-a i*rowNormalizer (∑ j, star (a j)*a j)) *
      (a i-a i*rowNormalizer (∑ j, star (a j)*a j))) =
    (1-rowNormalizer (∑ j, star (a j)*a j))*(∑ j, star (a j)*a j)*
      (1-rowNormalizer (∑ j, star (a j)*a j)) := by
  have hs := (IsSelfAdjoint.one A).sub
    (rowNormalizer_nonneg (∑ j, star (a j)*a j)).isSelfAdjoint
  simp only [show ∀ i, a i-a i*rowNormalizer (∑ j, star (a j)*a j) =
    a i*(1-rowNormalizer (∑ j, star (a j)*a j)) from fun i => by noncomm_ring,
    star_mul,hs.star_eq,Finset.mul_sum,Finset.sum_mul,mul_assoc]

theorem rowNormalizer_pairing_bound (τ : TracialState A) (a : I → A)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) (u : A) (hu : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : (τ.functional (∑ i, star (a i)*a i)).re ≤ 1+δ)
    (herr : (τ.functional (CFC.abs ((∑ i, star (a i)*a i)-1))).re ≤ δ) :
    ‖τ.functional (u*(matrixSynthesis a T-
      matrixSynthesis (fun i => a i*rowNormalizer (∑ j, star (a j)*a j)) T))‖^2 ≤
        2*(2+δ)*δ := by
  let b : A := ∑ i, star (a i)*a i
  let c := rowNormalizer b
  have hclip := rowNormalizer_bounds (row_mass_nonneg a)
  have hbc : (τ.functional (c*b*c)).re ≤ 1 := by
    have h := τ.functional.monotone (show c*b*c ≤ 1 from sub_nonneg.mp hclip.1)
    exact (Complex.le_def.mp h).1.trans_eq (by change (τ.functional 1).re = 1; rw [τ.normalized]; rfl)
  have hbd : (τ.functional ((1-c)*b*(1-c))).re ≤ δ :=
    ((Complex.le_def.mp (τ.functional.monotone hclip.2.2)).1).trans herr
  have hs1 : (∑ i, traceTwoNorm τ (a i)^2) ≤ 1+δ := by
    simpa only [traceTwoNorm_sq,← Complex.re_sum,← map_sum] using hmass
  have hs2 : (∑ i, traceTwoNorm τ (a i*c)^2) ≤ 1 := by
    simpa only [c,b,traceTwoNorm_sq,← Complex.re_sum,← map_sum,rowNormalizer_mass] using hbc
  have hs3 : (∑ i, traceTwoNorm τ (a i-a i*c)^2) ≤ δ := by
    simpa only [c,b,traceTwoNorm_sq,← Complex.re_sum,← map_sum,rowNormalizer_error_mass] using hbd
  have h := matrixSynthesis_difference_pairing τ a (fun i => a i*c) T hT u hu
  apply h.trans
  have hnon : 0 ≤ (∑ i, traceTwoNorm τ (a i)^2)+(∑ i, traceTwoNorm τ (a i*c)^2) :=
    add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  apply mul_le_mul
  · linarith
  · exact hs3
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · positivity

end Normalization

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.KrausApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA


section

noncomputable section

open scoped ComplexOrder

open CurrentMain Pureness

namespace NuclearTrace

section TracePairing

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_norm_mul_positive (τ : TracialState A) (u : A) (hu : ‖u‖ ≤ 1)
    {b : A} (hb : 0 ≤ b) : ‖τ.functional (u*b)‖ ≤ (τ.functional b).re := by
  let r := CFC.sqrt b
  have hr : star r = r := (CFC.sqrt_nonneg b).star_eq
  have he : τ.functional (u*b) = τ.functional ((r*u)*r) := by
    rw [τ.tracial (r*u) r]
    rw [← mul_assoc,CFC.sqrt_mul_sqrt_self b hb,τ.tracial]
  rw [he]
  apply (trace_norm_mul_le τ _ _).trans
  have hmul : traceTwoNorm τ (r*u) ≤ traceTwoNorm τ r :=
    (traceTwoNorm_mul_right τ u r).trans
      ((mul_le_mul_of_nonneg_right hu (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _))
  calc
    _ ≤ traceTwoNorm τ r * traceTwoNorm τ r :=
      mul_le_mul_of_nonneg_right hmul (traceTwoNorm_nonneg τ _)
    _ = (τ.functional b).re := by
      rw [← pow_two,traceTwoNorm_sq,hr,CFC.sqrt_mul_sqrt_self b hb]

lemma trace_norm_mul_selfAdjoint (τ : TracialState A) (u : A) (hu : ‖u‖ ≤ 1)
    {b : A} (hb : IsSelfAdjoint b) : ‖τ.functional (u*b)‖ ≤ traceOneNorm τ b := by
  calc
    _ = ‖τ.functional (u*b⁺)-τ.functional (u*b⁻)‖ := by
      rw [← map_sub,← mul_sub,CFC.posPart_sub_negPart b hb]
    _ ≤ ‖τ.functional (u*b⁺)‖+‖τ.functional (u*b⁻)‖ := norm_sub_le _ _
    _ ≤ (τ.functional b⁺).re+(τ.functional b⁻).re := add_le_add
      (trace_norm_mul_positive τ u hu (CFC.posPart_nonneg b))
      (trace_norm_mul_positive τ u hu (CFC.negPart_nonneg b))
    _ = traceOneNorm τ b := by
      rw [← Complex.add_re,← map_add,CFC.posPart_add_negPart b hb]
      rfl

end TracePairing

section Coefficients

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype I] [DecidableEq I]

lemma residualCoefficient_synthesis (i₀ : I) (r : A) (hr : 0 ≤ r)
    (T : CStarMatrix I I ℂ) :
    matrixSynthesis (residualCoefficient i₀ r) T = T i₀ i₀ • r := by
  change (∑ i, ∑ j, T i j • (star (residualCoefficient i₀ r i)*residualCoefficient i₀ r j)) = _
  simp [residualCoefficient,apply_ite,ite_mul,(CFC.sqrt_nonneg r).star_eq,
    CFC.sqrt_mul_sqrt_self r hr]

lemma residualCoefficient_mass (i₀ : I) (r : A) (hr : 0 ≤ r) :
    (∑ i, star (residualCoefficient i₀ r i)*residualCoefficient i₀ r i) = r := by
  simpa [matrixSynthesis_one,CStarMatrix.one_apply] using
    residualCoefficient_synthesis i₀ r hr 1

lemma residualCoefficient_pairing (τ : TracialState A) (i₀ : I) (r : A) (hr : 0 ≤ r)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) (u : A) (hu : ‖u‖ ≤ 1) :
    ‖τ.functional (u*matrixSynthesis (residualCoefficient i₀ r) T)‖ ≤ (τ.functional r).re := by
  rw [residualCoefficient_synthesis i₀ r hr T,mul_smul_comm,map_smul,norm_smul]
  have hentry : ‖T i₀ i₀‖ ≤ 1 := (show ‖T i₀ i₀‖ ≤ ‖T‖ from CStarMatrix.norm_entry_le_norm).trans hT
  exact (mul_le_mul hentry (trace_norm_mul_positive τ u hu hr)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Coefficients

section NormalizeSystem

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace FiniteCoefficientSystem

lemma residual_nonneg (F : FiniteCoefficientSystem A) : 0 ≤ F.residual :=
  (rowNormalizer_bounds (row_mass_nonneg F.coefficient)).1

omit [PartialOrder A] [StarOrderedRing A] in
lemma output_one (F : FiniteCoefficientSystem A) : F.output 1 = F.mass := by
  change matrixSynthesis F.coefficient (F.input 1) = _
  rw [F.input_one,matrixSynthesis_one]
  rfl

lemma normalize_output_one (F : FiniteCoefficientSystem A) (i₀ : F.Index) :
    (F.normalize i₀).output 1 = 1 := by
  rw [normalize,add_output,output_one,output_one]
  change (∑ i, star (F.coefficient i*rowNormalizer F.mass)*(F.coefficient i*rowNormalizer F.mass)) +
    (∑ i, star (residualCoefficient i₀ F.residual i)*residualCoefficient i₀ F.residual i) = 1
  rw [residualCoefficient_mass i₀ F.residual F.residual_nonneg]
  change (∑ i, star (F.coefficient i*rowNormalizer (∑ j, star (F.coefficient j)*F.coefficient j))*
    (F.coefficient i*rowNormalizer (∑ j, star (F.coefficient j)*F.coefficient j))) + _ = _
  rw [rowNormalizer_mass]
  change rowNormalizer F.mass*F.mass*rowNormalizer F.mass +
    (1-rowNormalizer F.mass*F.mass*rowNormalizer F.mass) = 1
  abel

lemma normalize_pairing (F : FiniteCoefficientSystem A) (i₀ : F.Index)
    (τ : TracialState A) (x u : A) (hx : ‖x‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : (τ.functional F.mass).re ≤ 1+δ)
    (herr : traceOneNorm τ (F.mass-1) ≤ δ) :
    ‖τ.functional (u*(F.output x-(F.normalize i₀).output x))‖ ≤
      Real.sqrt (2*(2+δ)*δ)+δ := by
  have hT : ‖F.input x‖ ≤ 1 := (F.input_norm x).trans hx
  have hclip := rowNormalizer_pairing_bound τ F.coefficient (F.input x) hT u hu hδ hmass herr
  have hc : ‖τ.functional (u*(F.output x-F.clip.output x))‖ ≤ Real.sqrt (2*(2+δ)*δ) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).2 hclip
  have hrmass : (τ.functional F.residual).re ≤ δ :=
    ((Complex.le_def.mp (τ.functional.monotone
      (rowNormalizer_bounds (row_mass_nonneg F.coefficient)).2.1)).1).trans herr
  have hr : ‖τ.functional (u*(F.fill i₀).output x)‖ ≤ δ :=
    (residualCoefficient_pairing τ i₀ F.residual F.residual_nonneg (F.input x) hT u hu).trans hrmass
  rw [normalize,add_output]
  have he : u*(F.output x-(F.clip.output x+(F.fill i₀).output x)) =
    u*(F.output x-F.clip.output x)-u*(F.fill i₀).output x := by noncomm_ring
  rw [he,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add hc hr)

end FiniteCoefficientSystem

end NormalizeSystem

lemma exists_clipping_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 2*δ+Real.sqrt (2*(2+δ)*δ) < ε := by
  let δ : ℝ := min 1 (min (ε/8) (ε^2/128))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := min_le_left _ _
  have he1 : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : δ ≤ ε^2/128 := (min_le_right _ _).trans (min_le_right _ _)
  have hb : 2*(2+δ)*δ ≤ (ε/4)^2 := by
    have hm := mul_le_mul_of_nonneg_right hd1 hd.le
    nlinarith
  have hs : Real.sqrt (2*(2+δ)*δ) ≤ ε/4 :=
    (Real.sqrt_le_iff).2 ⟨by positivity,hb⟩
  exact ⟨δ,hd,hd1,by linarith⟩

section NuclearNormalizedApproximation

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

theorem nuclear_uniform_normalized_finite_approximation
    (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (hT : Nonempty (TracialState A)) (x : I → selfAdjoint A)
    (hx : ∀ i, ‖(x i : A)‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : FiniteCoefficientSystem A, F.output 1 = 1 ∧
      ∀ τ : TracialState A, ∀ i : I, ∀ u : A, ‖u‖ ≤ 1 →
        ‖τ.functional (u*((x i : A)-F.output (x i)))‖ < ε := by
  classical
  obtain ⟨δ,hδ,hδ1,hδsmall⟩ := exists_clipping_tolerance hε
  let y : Unit ⊕ I → selfAdjoint A := Sum.elim (fun _ => 1) x
  obtain ⟨L,hL,hclose⟩ := nuclear_uniform_tracial_coefficient_approximation
    hA α hα hT y hδ
  obtain ⟨F,hF⟩ := coefficientCone_finite_system α L hL
  have hc (τ : TracialState A) (j : Unit ⊕ I) :
      traceOneNorm τ ((y j : A)-F.output (y j)) < δ := by
    rw [← hF]
    exact (Finset.single_le_sum (fun k _ => traceOneNorm_nonneg τ ((y k : A)-L (y k)))
      (Finset.mem_univ j)).trans_lt (hclose τ)
  have h1 (τ : TracialState A) : traceOneNorm τ (1-F.output 1) < δ := hc τ (.inl ())
  have hne : Nonempty F.Index := by
    by_contra hn
    let : IsEmpty F.Index := not_nonempty_iff.mp hn
    have hzero : F.output 1 = 0 := by rw [F.output_one]; simp [FiniteCoefficientSystem.mass]
    obtain ⟨τ⟩ := hT
    have h := h1 τ
    rw [hzero,sub_zero] at h
    have he : traceOneNorm τ 1 = 1 := by simp [traceOneNorm,τ.normalized]
    rw [he] at h
    linarith
  let i₀ : F.Index := Classical.choice hne
  refine ⟨F.normalize i₀,F.normalize_output_one i₀,?_⟩
  intro τ i u hu
  have herr : traceOneNorm τ (F.mass-1) ≤ δ := by
    have he : F.mass-1 = -(1-F.output 1) := by rw [F.output_one]; abel
    rw [he,traceOneNorm_neg]
    exact (h1 τ).le
  have hmass : (τ.functional F.mass).re ≤ 1+δ := by
    have hi := (trace_mass_difference_abs_le τ
      ((row_mass_nonneg F.coefficient).isSelfAdjoint.sub (IsSelfAdjoint.one A))).trans herr
    simp only [map_sub,τ.normalized,Complex.sub_re,Complex.one_re] at hi
    have hn := (abs_le.mp hi).2
    change (τ.functional (∑ j, star (F.coefficient j)*F.coefficient j)).re ≤ 1+δ
    linarith
  have hn := F.normalize_pairing i₀ τ (x i) u (hx i) hu hδ.le hmass herr
  have hsa : IsSelfAdjoint ((x i : A)-F.output (x i)) := by
    rw [← hF]
    exact (x i).property.sub (L (x i)).property
  have ho : ‖τ.functional (u*((x i : A)-F.output (x i)))‖ < δ :=
    (trace_norm_mul_selfAdjoint τ u hu hsa).trans_lt (hc τ (.inr i))
  have he : u*((x i : A)-(F.normalize i₀).output (x i)) =
      u*((x i : A)-F.output (x i))+u*(F.output (x i)-(F.normalize i₀).output (x i)) := by
    noncomm_ring
  rw [he,map_add]
  apply (norm_add_le _ _).trans_lt
  have hb := add_lt_add_of_lt_of_le ho hn
  exact hb.trans_le (by linarith)

end NuclearNormalizedApproximation

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PartitionAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace NuclearTrace

open Pureness CurrentMain

section ComplexApproximation

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype I]

theorem nuclear_uniform_finite_approximation
    (hA : IsNuclear.{0,0} A) (hT : Nonempty (TracialState A))
    (x : I → A) (hx : ∀ i, ‖x i‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : FiniteCoefficientSystem A, F.output 1 = 1 ∧
      ∀ τ : TracialState A, ∀ i : I, ∀ u : A, ‖u‖ ≤ 1 →
        ‖τ.functional (u*(x i-F.output (x i)))‖ < ε := by
  let y : I ⊕ I → selfAdjoint A := Sum.elim (fun i => ℜ (x i)) (fun i => ℑ (x i))
  have hy : ∀ j, ‖(y j : A)‖ ≤ 1 := by
    intro j
    cases j with
    | inl i => exact (realPart.norm_le _).trans (hx i)
    | inr i => exact (imaginaryPart.norm_le _).trans (hx i)
  obtain ⟨F,hF,hclose⟩ := nuclear_uniform_normalized_finite_approximation hA
    (stateHilbertRepresentation A) (stateHilbertRepresentation_injective A) hT y hy
    (show 0 < ε/2 by positivity)
  refine ⟨F,hF,?_⟩
  intro τ i u hu
  have hr := hclose τ (.inl i) u hu
  have hi := hclose τ (.inr i) u hu
  have he : u*(x i-F.output (x i)) =
      u*((ℜ (x i) : A)-F.output (ℜ (x i)))+
      Complex.I • (u*((ℑ (x i) : A)-F.output (ℑ (x i)))) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart (x i)]
    simp only [map_add,map_smul,mul_sub,mul_add,mul_smul_comm,smul_sub]
    abel
  rw [he,map_add,map_smul]
  apply (norm_add_le _ _).trans_lt
  rw [norm_smul,Complex.norm_I,one_mul]
  change ‖τ.functional (u*((y (.inl i) : A)-F.output (y (.inl i))))‖+
    ‖τ.functional (u*((y (.inr i) : A)-F.output (y (.inr i))))‖ < ε
  linarith

end ComplexApproximation

section Synthesis

variable {A N : Type} [CStarAlgebra A] [Fintype N] [DecidableEq N]

lemma matrixSynthesis_scalarMatrixUnit (a : N → A) (i j : N) :
    matrixSynthesis a (scalarMatrixUnit i j) = star (a i)*a j := by
  change (∑ k, ∑ l, scalarMatrixUnit i j k l • (star (a k)*a l)) = _
  simp [scalarMatrixUnit,Matrix.single_apply,ite_and]

end Synthesis

section NuclearGlobalAveraging

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem nuclear_global_partition_averaging
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hT : Nonempty (TracialState D))
    (K : Finset (unitary A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Type) (_ : Fintype N) (a : N → A),
      (∑ i, star (a i)*a i = 1) ∧ (∑ i, a i*star (a i) = 1) ∧
      ∀ x ∈ K, ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ ((∑ i, star (ι (a i))*q j*ι (a i)) -
        star (ι (x : A))*(∑ i, star (ι (a i))*q j*ι (a i))*ι (x : A)))^2 < ε := by
  classical
  have hTA : Nonempty (TracialState A) := ⟨pullbackTrace (Classical.choice hT) ι⟩
  have hx (x : K) : ‖(x.1 : A)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x.1 (1 : A)
    simpa only [mul_one] using h.trans_le (IsStarProjection.norm_le (1 : A) (IsStarProjection.one A))
  obtain ⟨F,hF,hclose⟩ := nuclear_uniform_finite_approximation hA hTA
    (fun x : K => (x.1 : A)) hx (show 0 < ε/8 by positivity)
  let φ : CStarMatrix F.Index F.Index ℂ →ₗ[ℂ] A := matrixSynthesis F.coefficient
  have hQ : 0 ≤ CStarMatrix.ofMatrix (fun i j => φ (scalarMatrixUnit i j)) := by
    simpa only [φ,matrixSynthesis_scalarMatrixUnit] using coefficient_choi_nonneg F.coefficient
  have hφ : φ 1 = 1 := by
    have he : F.output 1 = φ (F.input 1) := rfl
    rwa [he,F.input_one] at hF
  obtain ⟨a,ha1,ha2,ha⟩ := choi_bistochastic_family
    (CStarMatrix.ofMatrix (fun i j => φ (scalarMatrixUnit i j))) hQ (by
      change (∑ i, φ (scalarMatrixUnit i i)) = 1
      rw [← map_sum,sum_scalarMatrixUnit_diag,hφ])
  refine ⟨F.Index × F.Index,inferInstance,a,ha1,ha2,?_⟩
  intro x hxK J _ q hq hsum τ
  let T := F.input (x : A)
  have hTnorm : ‖T‖ ≤ 1 := (F.input_norm _).trans (hx ⟨x,hxK⟩)
  let φD : CStarMatrix F.Index F.Index ℂ →ₗ[ℂ] D := ι.toLinearMap.comp φ
  have haD (i j : F.Index) : φD (scalarMatrixUnit i j) =
      ∑ k, star (ι (a (k,i)))*ι (a (k,j)) := by
    change ι (φ (scalarMatrixUnit i j)) = _
    rw [show φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i))*a (k,j) from ha i j]
    simp only [map_sum,map_mul,map_star]
  have ha1D : (∑ i, star (ι (a i))*ι (a i)) = 1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι ha1
  obtain ⟨b,v,hb,hv,hb1,hv1,herr⟩ := choi_coupling φD (fun i => ι (a i))
    haD ha1D T hTnorm (mapUnitary ι x)
  have h := choi_global_partition_pairing τ b v
    (φD T) (mapUnitary ι x) hb1 hv1 herr q hq hsum
  have he : ‖(pullbackTrace τ ι).functional
      (star (x : A)*((x : A)-F.output (x : A)))‖ < ε/8 :=
    hclose (pullbackTrace τ ι) ⟨x,hxK⟩ (star (x : A)) (by simpa only [norm_star] using hx ⟨x,hxK⟩)
  have hpair : (τ.functional (star (ι (x : A))*(ι (x : A)-ι (φ T)))).re < ε/8 := by
    apply (Complex.re_le_norm _).trans_lt
    change ‖τ.functional (ι (star (x : A)*((x : A)-F.output (x : A))))‖ < ε/8 at he
    simpa only [map_mul,map_star,map_sub,φ,T,FiniteCoefficientSystem.output,LinearMap.comp_apply] using he
  simp only [hb,hv,mapUnitary_coe] at h
  change _ ≤ 8*(τ.functional (star (ι (x : A))*(ι (x : A)-ι (φ T)))).re at h
  linarith

end NuclearGlobalAveraging

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.BlockAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI uJ


section

noncomputable section

namespace CurrentMain

open scoped ComplexOrder

section Bistochastic

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [DecidableEq I] in
lemma kraus_coefficient_norm (v : I → D) (hv : ∑ i, star (v i)*v i = 1) (i : I) :
    ‖v i‖ ≤ 1 := by
  have hle : star (v i)*v i ≤ 1 := by
    rw [← hv]
    exact Finset.single_le_sum (fun j _ => star_mul_self_nonneg (v j)) (Finset.mem_univ i)
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg (v i))).mpr hle
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (v i)]

lemma scalarRowGram_eigenvalue_le_of_trace (f : D →ₚ[ℂ] ℂ) (a : I → D)
    (ha : ((scalarRowGram f a).trace).re ≤ 1) (i : I) :
    (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1 := by
  let hG := scalarRowGram_posSemidef f a
  have he : ∑ j, hG.isHermitian.eigenvalues j = ((scalarRowGram f a).trace).re := by
    rw [hG.isHermitian.trace_eq_sum_eigenvalues,Complex.re_sum]
    exact Finset.sum_congr rfl (fun j _ => rfl)
  exact (Finset.single_le_sum (fun j _ => hG.eigenvalues_nonneg j)
    (Finset.mem_univ i)).trans (he ▸ ha)

omit [DecidableEq I] [StarOrderedRing D] in
lemma scalarRowGram_kraus_trace (f : D →ₚ[ℂ] ℂ) (v : I → D)
    (hv : ∑ i, star (v i)*v i = 1) {q : D} (hq : IsStarProjection q)
    (hfq : f q = 1) :
    ((scalarRowGram f (fun i => v i*q)).trace).re = 1 := by
  have hs : ∑ i, star (v i*q)*(v i*q) = q := by
    simp only [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc]
    simp only [← mul_assoc (star _) _ _,← Finset.sum_mul,← Finset.mul_sum,hv,
      one_mul,hq.isIdempotentElem.eq]
  simp only [Matrix.trace,Matrix.diag,scalarRowGram,← map_sum,hs,hfq,Complex.one_re]

theorem spectral_row_block_of_spectral_bound {q : D} (hq : IsStarProjection q)
    (f : D →ₚ[ℂ] ℂ) (a : I → D)
    (haq : ∀ i, a i * q = a i)
    (hcs : ∀ i, (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1)
    {M σ δ : ℝ} (hM : 0 ≤ M) (hasum : ∑ i, ‖a i‖ ≤ M)
    (hσ : 0 < σ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ δ)
    (K : Finset D)
    (htest : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ δ)
    (hKn : ∀ x ∈ K, ‖x‖ ≤ 1)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 *
      ((Fintype.card I : ℝ) ^ 2 * δ)) ≤ 1 / 2) :
    let c := (scalarRowGram_posSemidef f a).isHermitian.eigenvalues
    let E := 2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M *
      ((Fintype.card I : ℝ) ^ 2 * δ)
    ∃ U : ProjectionRow {i : I // σ ≤ c i} q,
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ ((∑ i : {i : I // σ ≤ c i}, c i • U.atom i) -
          ∑ i, a i * star (a i)) ≤
          ((Fintype.card I : ℝ) * ((M + 1) * E + (σ + (Fintype.card I : ℝ) ^ 2 * δ))) *
            (τ.functional q).re) ∧
      (∀ x ∈ K, ∃ H : Matrix {i : I // σ ≤ c i} {i : I // σ ≤ c i} ℂ,
        ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤
          E * (1 + (Real.sqrt σ)⁻¹ * M) + (Real.sqrt σ)⁻¹ ^ 2 *
            ((Fintype.card I : ℝ) ^ 2 * δ)) := by
  classical
  dsimp only
  let c := (scalarRowGram_posSemidef f a).isHermitian.eigenvalues
  let Z := (scalarRowGram_posSemidef f a).isHermitian.eigenvectorUnitary
  let b := rotateRow a Z
  let Δ := (Fintype.card I : ℝ) ^ 2 * δ
  let E := 2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * Δ
  have hc (i : I) : 0 ≤ c i := (scalarRowGram_posSemidef f a).eigenvalues_nonneg i
  have hc1 (i : I) : c i ≤ 1 := hcs i
  have hbsupp (i : I) : b i * q = b i := rotateRow_right_support a haq Z i
  have hbn (i : I) : ‖b i‖ ≤ M := (rotateRow_norm_le a Z i).trans hasum
  have hΔ : 0 ≤ Δ := mul_nonneg (sq_nonneg _) hδ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbg (i j : I) : ‖star (b i) * b j - (if i = j then c i • q else 0)‖ ≤ Δ :=
    rowPair_spectral_rotation f a hgram i j
  obtain ⟨U, hU, hU'⟩ := normalize_retained_spectrum hq b c hc hc1 hbsupp
    hσ hM hΔ hbn hbg hsmall
  refine ⟨U, ?_, ?_⟩
  · intro τ
    have he := retained_spectrum_trace_error hq b c hc hc1 hbsupp hM hE
      (add_nonneg hσ.le hΔ) hbn (fun i => by simpa using hbg i i) U hU' τ
    rw [rotateRow_covariance a Z] at he
    exact he
  · intro x hx
    obtain ⟨H, hH⟩ := htest x hx
    let H' : Matrix I I ℂ := star (Z : Matrix I I ℂ) * H * Z
    let r : {i : I // σ ≤ c i} → ℝ := fun i => (Real.sqrt (c i))⁻¹
    have hr (i : {i : I // σ ≤ c i}) : 0 ≤ r i := by dsimp [r]; positivity
    have hrL (i : {i : I // σ ≤ c i}) : r i ≤ (Real.sqrt σ)⁻¹ :=
      (inv_le_inv₀ (Real.sqrt_pos.mpr (hσ.trans_le i.property))
        (Real.sqrt_pos.mpr hσ)).mpr (Real.sqrt_le_sqrt i.property)
    refine ⟨fun i j => (r i * r j) • H' i j, fun i j => ?_⟩
    apply normalized_rowPair_error U (fun i => b i) r x (hKn x hx)
      (fun i j => H' i j) hr (by positivity) hrL (fun i => hbn i) hU
    exact fun i j => rowPair_rotate_error a Z x H hH i j

end Bistochastic

section RawKraus

variable {I : Type} {D : Type uD} [Fintype I] [CStarAlgebra D] [DecidableEq D]
  [PartialOrder D] [StarOrderedRing D]

theorem raw_kraus_spectral_block (v : I → D) (hv : ∑ i, star (v i)*v i = 1)
    (K : Finset D) (hK : ∀ x ∈ K, ‖x‖ ≤ 1) {η : ℝ}
    (T : BlockControl (Fintype.card I) η)
    {q : D} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hcomp : ∀ i j, ∀ x ∈ insert 1 K, ∃ α : ℂ,
      ‖q * (star (v i) * x * v j) * q - α • q‖ < T.tolerance / 2) :
    ∃ n : ℕ, n ≤ Fintype.card I ∧ ∃ U : ProjectionRow (Fin n) q, ∃ c : Fin n → ℝ,
      (∀ i, 0 ≤ c i) ∧ (∀ i, c i ≤ 1) ∧ Monotone c ∧
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ ((∑ i, c i • U.atom i) - weightedAverage (fun _ => 1) v q) ≤
          η ^ 2 * (τ.functional q).re) ∧
      (∀ k : ℕ, ∀ e : Fin k ↪ Fin n, ∀ x ∈ K, ∃ H : Matrix (Fin k) (Fin k) ℂ,
        ‖(U.subrow e).sample q * x * (U.subrow e).sample q - (U.subrow e).matrix q H‖ < η) := by
  classical
  obtain ⟨f, hf, hfq⟩ := exists_state_at_projection hq hq0
  let a : I → D := fun i => v i*q
  have hcs (i : I) : (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1 :=
    scalarRowGram_eigenvalue_le_of_trace f a
      (scalarRowGram_kraus_trace f v hv hq hfq).le i
  have ha (i : I) : ‖a i‖ ≤ 1 := by
    exact (norm_mul_le _ _).trans
      ((mul_le_mul (kraus_coefficient_norm v hv i) hq.norm_le
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hasum : ∑ i, ‖a i‖ ≤ Fintype.card I := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ha i)
  have hscalar (i j : I) (x : D) (hx : x ∈ insert 1 K) :
      ‖rowPair a x i j - f (rowPair a x i j) • q‖ ≤ T.tolerance := by
    obtain ⟨c,hc⟩ := hcomp i j x hx
    have he := state_scalar_error f hf hq hfq (q * (star (v i)*x*v j)*q) c
    have hrow : rowPair a x i j = q * (star (v i)*x*v j)*q := by
      simp only [rowPair,a,star_mul,hq.isSelfAdjoint.star_eq,mul_assoc]
    rw [hrow]
    linarith
  have hgram (i j : I) : ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ T.tolerance := by
    simpa only [scalarRowGram, rowPair, mul_one] using hscalar i j 1 (Finset.mem_insert_self _ _)
  have htests : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ T.tolerance := by
    intro x hx
    exact ⟨fun i j => f (rowPair a x i j), fun i j => hscalar i j x (Finset.mem_insert_of_mem hx)⟩
  obtain ⟨U, htr, hpair⟩ := spectral_row_block_of_spectral_bound hq f a
    (fun i => by simp only [a,mul_assoc,hq.isIdempotentElem.eq]) hcs
    (Nat.cast_nonneg _) hasum T.cutoff_pos T.tolerance_pos.le
    hgram K htests hK T.inverse_control
  let c := (scalarRowGram_posSemidef f a).isHermitian.eigenvalues
  let J := {i : I // T.cutoff ≤ c i}
  let c' : J → ℝ := fun i => c i
  let e := sortedIndex c'
  let U' := U.sorted c'
  have hn : Fintype.card J ≤ Fintype.card I := Fintype.card_subtype_le _
  have hnR : (Fintype.card J : ℝ) ≤ Fintype.card I := by exact_mod_cast hn
  have heq : ∑ i, c' (e i) • U'.atom i = ∑ i : J, c i • U.atom i :=
    U.sorted_weighted_sum c'
  refine ⟨Fintype.card J, hn, U', c' ∘ e, ?_, ?_, sortedIndex_monotone c', ?_, ?_⟩
  · intro i
    exact (scalarRowGram_posSemidef f a).eigenvalues_nonneg (e i)
  · intro i
    exact hcs (e i)
  · intro τ
    simp only [Function.comp_apply]
    have hav : weightedAverage (fun _ : I => (1 : ℝ)) v q = ∑ i, a i*star (a i) := by
      simp only [weightedAverage,one_smul,a,star_mul,hq.isSelfAdjoint.star_eq,
        mul_assoc,← mul_assoc q q,hq.isIdempotentElem.eq]
    rw [heq,hav]
    exact (htr τ).trans (mul_le_mul_of_nonneg_right T.trace_control
      (τ.functional.map_nonneg hq.nonneg).1)
  · intro k g x hx
    obtain ⟨H, hH⟩ := hpair x hx
    let H' : Matrix (Fin (Fintype.card J)) (Fin (Fintype.card J)) ℂ := H.submatrix e e
    have hp (i j : Fin (Fintype.card J)) :
        ‖rowPair U'.entry x i j - H' i j • q‖ ≤
          rowCompressionError (Fintype.card I) T.cutoff T.tolerance := hH (e i) (e j)
    refine ⟨H'.submatrix g g, ?_⟩
    apply (U'.subrow_compression g x H'
      (rowCompressionError_nonneg (Nat.cast_nonneg _) T.tolerance_pos.le) hp).trans_lt
    apply lt_of_le_of_lt ?_ T.compression_control
    simp only [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (by gcongr)
      (rowCompressionError_nonneg (Nat.cast_nonneg _) T.tolerance_pos.le)

end RawKraus

section GlobalEnergy

variable {D : Type uD} {J : Type uJ} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Fintype J]

theorem layer_energy_global (τ : Pureness.TracialState D)
    (n : J → ℕ) (e : (j : J) → Fin (n j) → D)
    (he : ∀ j i, IsStarProjection (e j i))
    (ho : ∀ j, Pairwise (fun i k => e j i * e j k = 0))
    (c : (j : J) → Fin (n j) → ℝ) (hc : ∀ j i, 0 ≤ c j i)
    (hm : ∀ j, Monotone (c j)) (x : unitary D)
    (h : J → D) (hh : ∀ j, 0 ≤ h j) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hclose : ∑ j, traceOneNorm τ ((∑ i, c j i • e j i) - h j) ≤ η^2)
    (hmass : ∑ j, (τ.functional (h j)).re ≤ 1)
    (hcentral : ∑ j, traceOneNorm τ (h j - (x : D)*h j*star (x : D)) ≤ η^2) :
    ∑ j, ∑ i, orderedLayerWeights (c j) i * traceTwoNorm τ
      ((x : D)*upperLayerCut (e j) i - upperLayerCut (e j) i*(x : D))^2 ≤ 6*η := by
  classical
  let b : J → D := fun j => ∑ i, c j i • e j i
  let E : J → ℝ := fun j => ∑ i, orderedLayerWeights (c j) i * traceTwoNorm τ
    ((x : D)*upperLayerCut (e j) i - upperLayerCut (e j) i*(x : D))^2
  let m : J → ℝ := fun j => (τ.functional (b j)).re
  let d : J → ℝ := fun j => traceOneNorm τ (b j - (x : D)*b j*star (x : D))
  have hb (j) : 0 ≤ b j := projection_combination_nonneg (e j) (he j) (c j) (hc j)
  have hmn (j) : 0 ≤ m j := (τ.functional.map_nonneg (hb j)).1
  have hdn (j) : 0 ≤ d j := traceOneNorm_nonneg τ _
  have hEn (j) : 0 ≤ E j := Finset.sum_nonneg fun i _ =>
    mul_nonneg (orderedLayerWeights_nonneg (c j) (hc j) (hm j) i) (sq_nonneg _)
  have hmb : ∑ j, m j ≤ 1+η^2 := by
    have hz := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      trace_mass_perturb τ (hb j).isSelfAdjoint (hh j).isSelfAdjoint
        (le_refl (traceOneNorm τ (b j-h j))) (le_refl (τ.functional (h j)).re)
    dsimp only [m]
    simp only [Finset.sum_add_distrib] at hz
    exact hz.trans (add_le_add hmass hclose)
  have hdb : ∑ j, d j ≤ 3*η^2 := by
    have hz := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      trace_central_perturb τ (hb j).isSelfAdjoint (hh j).isSelfAdjoint x
        (le_refl (traceOneNorm τ (b j-h j)))
        (le_refl (traceOneNorm τ (h j-(x : D)*h j*star (x : D))))
    change (∑ j, d j) ≤ _ at hz
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hz
    linarith
  have hEsq (j) : (E j)^2 ≤ (4*m j)*d j := by
    have hl := layer_energy_le_of_orthogonal τ (e j) (he j) (ho j)
      (orderedLayerWeights (c j)) (orderedLayerWeights_nonneg (c j) (hc j) (hm j)) x
    have hs : ∑ i, orderedLayerWeights (c j) i • upperLayerCut (e j) i = b j := by
      rw [layer_decomposition]
      simp only [layerCoefficient_orderedLayerWeights]
      rfl
    rw [hs] at hl
    change E j ≤ 2*Real.sqrt (m j*d j) at hl
    have hsq := Real.sq_sqrt (mul_nonneg (hmn j) (hdn j))
    nlinarith [hEn j, Real.sqrt_nonneg (m j*d j)]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hmn j))
    (fun j _ => hdn j) (fun j _ => hEsq j)
  rw [← Finset.mul_sum] at hCS
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hmb (by norm_num : (0 : ℝ) ≤ 4))
    hdb (Finset.sum_nonneg (fun j _ => hdn j)) (by positivity : 0 ≤ 4*(1+η^2))
  have hηsq : η^2 ≤ 1 := by nlinarith
  have hbound : 4*(1+η^2)*(3*η^2) ≤ (6*η)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hηsq (sq_nonneg η)]
  have ht := hCS.trans (hprod.trans hbound)
  change (∑ j, E j) ≤ 6*η
  nlinarith

end GlobalEnergy

section KrausFamily

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing D] in
lemma kraus_average_trace {I : Type uI} [Fintype I] (τ : Pureness.TracialState D)
    (v : I → D) (hv : ∑ i, star (v i)*v i = 1) (q : D) :
    τ.functional (weightedAverage (fun _ : I => (1 : ℝ)) v q) = τ.functional q := by
  simp only [weightedAverage,one_smul,map_sum]
  calc
    _ = ∑ i, τ.functional ((star (v i)*v i)*q) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [τ.tracial (v i*q),← mul_assoc]
    _ = τ.functional q := by rw [← map_sum,← Finset.sum_mul,hv,one_mul]

theorem weighted_family_of_kraus_average {I : Type} [Fintype I]
    (hRR : RealRankZero D) (v : I → D) (hv : ∑ i, star (v i)*v i = 1)
    (K : Finset (unitary D)) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    {r : D} (hr : IsStarProjection r)
    (hcentral : ∀ P : ProjectionPartition r, ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
      ∑ s, traceOneNorm τ (weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) -
        (x : D) * weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) * star (x : D)) ≤ η^2) :
    ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j * (x : D) * F.range j - (F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage (fun _ : I => (1 : ℝ)) v r) ≤ η ^ 2) ∧
      (∀ x ∈ K, ∀ τ : Pureness.TracialState D,
        ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 ≤
          6 * η) := by
  classical
  obtain ⟨T⟩ := exists_blockControl (Fintype.card I) (Nat.cast_nonneg _) hη
  let K' : Finset D := K.image (fun x : unitary D => (x : D))
  let tests : Finset D := Finset.univ.biUnion fun i : I =>
    Finset.univ.biUnion fun j : I => (insert 1 K').image (fun x => star (v i) * x * v j)
  obtain ⟨P, hP⟩ := scalar_compressions hRR hr tests (half_pos T.tolerance_pos)
  have hcompression (s : P.Index) (i j : I) (x : D) (hx : x ∈ insert 1 K') :
      ∃ α : ℂ, ‖P.piece s * (star (v i) * x * v j) * P.piece s - α • P.piece s‖ <
        T.tolerance / 2 := by
    apply hP _ _ s
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩⟩
  have hK' (x : D) (hx : x ∈ K') : ‖x‖ ≤ 1 := by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have hu := CStarRing.norm_coe_unitary_mul u (1 : D)
    rw [mul_one] at hu
    exact hu.le.trans (IsStarProjection.one D).norm_le
  choose n hn U c hc hc1 hmono htr hpair using fun s =>
    raw_kraus_spectral_block v hv K' hK' T (P.isProjection s) (P.nonzero s) (hcompression s)
  let J := Σ s : P.Index, {j : Fin (n s) // 0 < orderedLayerWeights (c s) j}
  let F : WeightedBlockFamily r := {
    Index := J
    weight := fun a => orderedLayerWeights (c a.1) a.2
    weight_pos := fun a => a.2.property
    weight_le_one := fun a => (orderedLayerWeights_le (c a.1) (hc a.1) a.2).trans (hc1 a.1 a.2)
    base := fun a => P.piece a.1
    baseProjection := fun a => P.isProjection a.1
    base_nonzero := fun a => P.nonzero a.1
    base_le := fun a => P.piece_le hr a.1
    columns := fun a => Fintype.card {i : Fin (n a.1) // a.2.val ≤ i}
    columns_pos := fun a => upperColumn_nonempty a.2.val
    row := fun a => (U a.1).subrow (upperEmbedding a.2.val) }
  have hFsum : F.weightedSum = ∑ s, ∑ i, c s i • (U s).atom i := by
    change (∑ a : J, orderedLayerWeights (c a.1) a.2 •
      ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1)) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun s _ => (U s).positive_layer_sum (c s) (hc s) (hmono s)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro j x hx
    exact hpair j.1 _ (upperEmbedding j.2.val) (x : D) (Finset.mem_image_of_mem _ hx)
  · intro τ
    have hav : weightedAverage (fun _ : I => (1 : ℝ)) v r = ∑ s, weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) := by
      calc
        _ = weightedAverage (fun _ : I => (1 : ℝ)) v (∑ s, P.piece s) := congrArg (weightedAverage (fun _ : I => (1 : ℝ)) v) P.sum_eq.symm
        _ = _ := weightedAverage_sum (fun _ : I => (1 : ℝ)) v P.piece
    rw [hFsum, hav, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s, traceOneNorm τ ((∑ i, c s i • (U s).atom i) - weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s)) :=
        traceOneNorm_sum_le τ _ fun s =>
          (projection_combination_nonneg (U s).atom (U s).atom_projection (c s) (hc s)).isSelfAdjoint.sub
            (weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) (P.isProjection s).nonneg).isSelfAdjoint
      _ ≤ ∑ s, η ^ 2 * (τ.functional (P.piece s)).re := Finset.sum_le_sum fun s _ => htr s τ
      _ = η ^ 2 * (τ.functional r).re := by rw [← Finset.mul_sum, ← Complex.re_sum, ← map_sum, P.sum_eq]
      _ ≤ η ^ 2 := by
        have ht := trace_projection_le_one τ hr
        nlinarith [sq_nonneg η]
  · intro x hx τ
    change (∑ a : J, orderedLayerWeights (c a.1) a.2 * traceTwoNorm τ
      ((x : D) * ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1) -
        ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1) * (x : D)) ^ 2) ≤ _
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ s, ∑ j, orderedLayerWeights (c s) j * traceTwoNorm τ
          ((x : D) * upperLayerCut (U s).atom j - upperLayerCut (U s).atom j * (x : D)) ^ 2 :=
        Finset.sum_congr rfl fun s _ => (U s).positive_layer_energy (c s) (hc s) (hmono s) τ x
      _ ≤ 6*η := by
        apply layer_energy_global τ n (fun s => (U s).atom)
          (fun s => (U s).atom_projection) (fun s => (U s).atom_orthogonal)
          c hc hmono x (fun s => weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s))
          (fun s => weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one)
            (P.isProjection s).nonneg) hη.le hη1.le
        · calc
            _ ≤ ∑ s, η^2*(τ.functional (P.piece s)).re := Finset.sum_le_sum fun s _ => htr s τ
            _ = η^2*(τ.functional r).re := by
              rw [← Finset.mul_sum,← Complex.re_sum,← map_sum,P.sum_eq]
            _ ≤ η^2 := by
              have ht := trace_projection_le_one τ hr
              nlinarith [sq_nonneg η]
        · simp only [kraus_average_trace τ v hv]
          rw [← Complex.re_sum,← map_sum,P.sum_eq]
          exact trace_projection_le_one τ hr
        · exact hcentral P x hx τ

end KrausFamily

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.NuclearFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open Pureness NuclearTrace

open scoped ComplexOrder

namespace CurrentMain

section NuclearWeightedBlocks

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma global_partition_bound_corner {N : Type} [Fintype N]
    (v : N → D) (x : unitary D) {r : D} (hr : IsStarProjection r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (q j) -
        (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (q j)*star (x : D)))^2 < δ^2)
    (P : ProjectionPartition r) (τ : TracialState D) :
    (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j) -
      (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D))) ≤ δ := by
  classical
  let q : Option P.Index → D := Option.elim' (1-r) P.piece
  have hq : ∀ j, IsStarProjection (q j) := by
    intro j
    cases j with
    | none => exact hr.one_sub
    | some j => exact P.isProjection j
  have hs : ∑ j, q j = 1 := by
    rw [Fintype.sum_option]
    change (1-r)+(∑ j, P.piece j) = 1
    rw [P.sum_eq]
    abel
  have hb := h (Option P.Index) q hq hs τ
  rw [Fintype.sum_option] at hb
  change (traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)*star (x : D))+
    (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D))))^2 < δ^2 at hb
  have hnon := traceOneNorm_nonneg τ
    (weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)*star (x : D))
  have hsum : 0 ≤ ∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)-
      (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D)) :=
    Finset.sum_nonneg fun j _ => traceOneNorm_nonneg τ _
  nlinarith

theorem nuclear_weighted_block_family
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (N : Type) (_ : Fintype N) (v : N → A),
      (∑ i, star (v i)*v i = 1) ∧ (∑ i, v i*star (v i) = 1) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : TracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage (fun _ : N => (1 : ℝ))
          (fun i => ι (v i)) r) ≤ η^2) ∧
      (∀ x ∈ K, ∀ τ : TracialState D,
        ∑ j, F.weight j*traceTwoNorm τ (ι (x : A)*F.range j-F.range j*ι (x : A))^2 ≤ 6*η) := by
  classical
  let K' := K.image (fun x => star x)
  obtain ⟨N,instN,a,ha1,ha2,ha⟩ := nuclear_global_partition_averaging hA ι hT K'
    (show 0 < (η^2)^2 by positivity)
  let v : N → A := fun i => star (a i)
  have hv : ∑ i, star (v i)*v i = 1 := by simpa only [v,star_star] using ha2
  have hv' : ∑ i, v i*star (v i) = 1 := by simpa only [v,star_star] using ha1
  have hvD : ∑ i, star (ι (v i))*ι (v i) = 1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι hv
  refine ⟨N,instN,v,hv,hv',?_⟩
  intro r hr
  let KD := K.image (mapUnitary ι)
  have hc : ∀ P : ProjectionPartition r, ∀ x ∈ KD, ∀ τ : TracialState D,
      ∑ s, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) (P.piece s) -
        (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) (P.piece s)*star (x : D)) ≤ η^2 := by
    intro P x hx τ
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply global_partition_bound_corner (fun i => ι (v i)) (mapUnitary ι y) hr (sq_nonneg η) _ P τ
    intro J _ q hq hsum σ
    have he := ha (star y) (Finset.mem_image_of_mem _ hy) J q hq hsum σ
    simpa only [weightedAverage,one_smul,v,map_star,star_star,Unitary.coe_star,mapUnitary_coe] using he
  obtain ⟨F,hcompress,hmass,henergy⟩ := weighted_family_of_kraus_average hRR
    (fun i => ι (v i)) hvD KD hη hη1 hr hc
  refine ⟨F,?_,hmass,?_⟩
  · intro j x hx
    exact hcompress j (mapUnitary ι x) (Finset.mem_image_of_mem _ hx)
  · intro x hx
    exact henergy (mapUnitary ι x) (Finset.mem_image_of_mem _ hx)

end NuclearWeightedBlocks

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.BistochasticTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

namespace BistochasticTest

variable {A D : Type} [CStarAlgebra A] [CStarAlgebra D]

variable [PartialOrder D] [StarOrderedRing D]

lemma relative_unitary_tests [PartialOrder A] [StarOrderedRing A]
    (V : BistochasticTest A) (ι : A →⋆ₐ[ℂ] D) :
    ∃ L : Finset (unitary A), ∀ (J : Type) [Fintype J] (y : J → D)
      (τ : TracialState D) (B : ℝ), 0 ≤ B →
      (∀ u ∈ L, ∑ j, traceTwoNorm τ (ι (u : A)*y j-y j*ι (u : A))^2 ≤ B) →
      ∑ j, (V.map ι).energy τ (y j) ≤ (4*V.size)*B := by
  classical
  choose u c he hc using fun i => CStarAlgebra.exists_sum_four_unitary (V.coeff i)
  let L := Finset.univ.biUnion fun i : Fin V.size => Finset.univ.image (u i)
  refine ⟨L,?_⟩
  intro J _ y τ B _ hB
  have hb (i : Fin V.size) (j : J) :
      traceTwoNorm τ (ι (V.coeff i)*y j-y j*ι (V.coeff i))^2 ≤
        ∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))^2 := by
    have hd : ι (V.coeff i)*y j-y j*ι (V.coeff i) =
        ∑ k : Fin 4, c i k • (ι (u i k : A)*y j-y j*ι (u i k : A)) := by
      rw [he i,map_sum]
      simp only [map_smul]
      rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
      simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
    have hnorm : traceTwoNorm τ (ι (V.coeff i)*y j-y j*ι (V.coeff i)) ≤
        (1/2 : ℝ)*(∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))) := by
      rw [hd]
      apply (traceTwoNorm_sum_le _ τ _).trans
      simp only [traceTwoNorm_smul,Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
        ((hc i k).trans (by linarith [kraus_coefficient_norm V.coeff V.col i])) (traceTwoNorm_nonneg τ _)
    have hs := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun k : Fin 4 => traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A)))
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hs
    have hn := traceTwoNorm_nonneg τ (ι (V.coeff i)*y j-y j*ι (V.coeff i))
    have hsum : 0 ≤ ∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A)) :=
      Finset.sum_nonneg fun _ _ => traceTwoNorm_nonneg τ _
    nlinarith
  calc
    _ ≤ ∑ j, ∑ i, ∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))^2 :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hb i j
    _ = ∑ i, ∑ k : Fin 4, ∑ j, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))^2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ i : Fin V.size, ∑ k : Fin 4, B := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun k _ => hB _ (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    _ = _ := by simp; ring

end BistochasticTest

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PreparedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

namespace BistochasticTest

variable {A D N : Type} [CStarAlgebra A] [CStarAlgebra D] [Fintype N]

lemma ofFamily_average (ι : A →⋆ₐ[ℂ] D) (v : N → A)
    (hcol : ∑ i, star (v i)*v i = 1) (hrow : ∑ i, v i*star (v i) = 1) (r : D) :
    weightedAverage (fun _ => (1 : ℝ)) ((ofFamily v hcol hrow).map ι).coeff r =
      weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) r := by
  simp only [weightedAverage,one_smul,map,ofFamily]
  exact (Fintype.equivFin N).symm.sum_comp (fun i => ι (v i)*r*star (ι (v i)))

end BistochasticTest

section Prepared

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem nuclear_prepared_row_blocks_oai
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A)) (S : Finset (BistochasticTest A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (M σ : ℝ) (L : Finset (unitary A)) (V : BistochasticTest A),
      1 ≤ M ∧ 0 < σ ∧ σ ≤ η ∧ M*σ ≤ η ∧ K ⊆ L ∧
      (∀ W ∈ S, ∀ (J : Type) [Fintype J] (y : J → D) (τ : TracialState D)
        (B : ℝ), 0 ≤ B →
        (∀ u ∈ L, ∑ j, traceTwoNorm τ (ι (u : A)*y j-y j*ι (u : A))^2 ≤ B) →
        ∑ j, (W.map ι).energy τ (y j) ≤ M*B) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
        (∀ j, ∀ x ∈ L, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
          ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) ∧
        (∀ τ : TracialState D,
          traceOneNorm τ (F.weightedSum-weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff r) ≤ η^2) ∧
        (∀ x ∈ L, ∀ τ : TracialState D,
          ∑ j, F.weight j*traceTwoNorm τ (ι (x : A)*F.range j-F.range j*ι (x : A))^2 ≤ 6*σ) := by
  classical
  choose L₀ hL₀ using fun W : BistochasticTest A => W.relative_unitary_tests ι
  let L := K ∪ S.biUnion L₀
  let M : ℝ := 1+∑ W ∈ S, 4*(W.size : ℝ)
  have hM : 1 ≤ M := by
    have hs : 0 ≤ ∑ W ∈ S, 4*(W.size : ℝ) := Finset.sum_nonneg fun W _ => by positivity
    dsimp [M]
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let σ := η/M
  have hσ : 0 < σ := div_pos hη hMpos
  have hση : σ ≤ η := (div_le_self hη.le hM)
  have hσ1 : σ < 1 := hση.trans_lt hη1
  obtain ⟨N,instN,v,hv,hv',hblocks⟩ := nuclear_weighted_block_family hA ι hRR hT L hσ hσ1
  let V := BistochasticTest.ofFamily v hv hv'
  refine ⟨M,σ,L,V,hM,hσ,hση,?_,Finset.subset_union_left,?_,?_⟩
  · dsimp [σ]; rw [mul_div_cancel₀ _ (ne_of_gt hMpos)]
  · intro W hW J _ y τ B hB htest
    have hcoeff : 4*(W.size : ℝ) ≤ M := by
      have hh := Finset.single_le_sum (f := fun W : BistochasticTest A => 4*(W.size : ℝ))
        (fun W _ => by positivity) hW
      dsimp [M]
      linarith
    exact (hL₀ W J y τ B hB (fun u hu => htest u
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨W,hW,hu⟩)))).trans
        (mul_le_mul_of_nonneg_right hcoeff hB)
  · intro r hr
    obtain ⟨F,hcomp,hmass,henergy⟩ := hblocks r hr
    refine ⟨F,hcomp,?_,henergy⟩
    intro τ
    rw [show (V.map ι).coeff = ((BistochasticTest.ofFamily v hv hv').map ι).coeff from rfl,
      BistochasticTest.ofFamily_average ι v hv hv' r]
    exact (hmass τ).trans ((sq_le_sq₀ hσ.le hη.le).mpr hση)

end Prepared

end CurrentMain

end

end

end OAI
end

theorem solution : type_of% @OAI.CurrentMain.nuclear_prepared_row_blocks_oai := @OAI.CurrentMain.nuclear_prepared_row_blocks_oai
