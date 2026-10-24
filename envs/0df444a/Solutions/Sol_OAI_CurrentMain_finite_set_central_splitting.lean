-- Prove2me | solution 1 for OAI.CurrentMain.finite_set_central_splitting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:14:47.542872+00:00
-- url     : https://prove2.me/submissions/30bf6306-07b3-45d0-b7e9-8053916b019d

import Mathlib
import Definitions.Def_UniformGamma
import Definitions.Def_OAIQWCMM000
import Theorems.Thm_OAI_CurrentMain_nuclear_prepared_row_blocks

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
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

lemma trace_unitary_commutator_square (τ : TracialState D) (x : unitary D)
    {p : D} (hp : IsStarProjection p) :
    τ.functional (star ((x : D) * p - p * (x : D)) *
      ((x : D) * p - p * (x : D))) =
    2 * τ.functional p - 2 * τ.functional
      (star (p * (x : D) * p) * (p * (x : D) * p)) := by
  have hpp : p * p = p := hp.isIdempotentElem
  have hsp : star p = p := hp.isSelfAdjoint
  have h1 : p * star (x : D) * ((x : D) * p) = p := by
    rw [mul_assoc, ← mul_assoc (star (x : D)), Unitary.coe_star_mul_self,
      one_mul, hpp]
  have h2 : star (x : D) * p * (p * (x : D)) =
      star (x : D) * p * (x : D) := by
    simp only [mul_assoc, ← mul_assoc p p, hpp]
  have ht : τ.functional (star (x : D) * p * (x : D)) = τ.functional p := by
    rw [τ.tracial (star (x : D) * p) (x : D)]
    rw [← mul_assoc, x.property.2, one_mul]
  have hcross : τ.functional (star (x : D) * p * ((x : D) * p)) =
      τ.functional (p * star (x : D) * (p * (x : D))) := by
    rw [τ.tracial (star (x : D) * p) ((x : D) * p)]
    simp only [mul_assoc]
    rw [τ.tracial (x : D) (p * (star (x : D) * p))]
    simp only [mul_assoc]
  have hcompress : τ.functional (star (p * (x : D) * p) *
      (p * (x : D) * p)) =
      τ.functional (p * star (x : D) * (p * (x : D))) := by
    simp only [star_mul, hsp]
    have he : p * (star (x : D) * p) * (p * (x : D) * p) =
        p * (star (x : D) * (p * (x : D))) * p := by
      simp only [mul_assoc, ← mul_assoc p p, hpp]
    rw [he, trace_projection_corner τ hp]
    simp only [mul_assoc]
  rw [hcompress]
  simp only [star_sub, star_mul, hsp, sub_mul, mul_sub, h1, h2,
    map_sub, ht, hcross]
  ring

end TraceIdentities

section TraceBounds

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sq (τ : TracialState D) (a : D) :
    traceTwoNorm τ a ^ 2 = (τ.functional (star a * a)).re := by
  exact Real.sq_sqrt (τ.functional.map_nonneg (star_mul_self_nonneg a)).1

lemma trace_norm_mul_le (τ : TracialState D) (a b : D) :
    ‖τ.functional (a * b)‖ ≤ traceTwoNorm τ a * traceTwoNorm τ b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.functional.toPreGNS (star a))
    (τ.functional.toPreGNS b)
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_star,
    ← traceTwoNorm_eq_gns, traceTwoNorm_star] using h

lemma unitary_commutator_energy (τ : TracialState D) (x : unitary D)
    {p : D} (hp : IsStarProjection p) :
    traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2 =
      2 * (τ.functional p).re - 2 * traceTwoNorm τ (p * (x : D) * p) ^ 2 := by
  simp only [traceTwoNorm_sq]
  rw [trace_unitary_commutator_square τ x hp]
  simp

end TraceBounds

section OrthogonalEnergy

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D]

lemma trace_commutator_square_expansion (τ : TracialState D)
    {p : D} (hp : IsStarProjection p) (x : D) :
    τ.functional (star (x * p - p * x) * (x * p - p * x)) =
      τ.functional (star x * x * p) + τ.functional (star x * p * x) -
        2 * τ.functional (p * star x * p * x) := by
  have hsp : star p = p := hp.isSelfAdjoint
  have hpp : p * p = p := hp.isIdempotentElem
  have h1 : τ.functional (p * star x * (x * p)) =
      τ.functional (star x * x * p) := by
    calc
      τ.functional (p * star x * (x * p)) =
          τ.functional (p * (star x * x) * p) := by simp only [mul_assoc]
      _ = τ.functional (p * (star x * x)) := trace_projection_corner τ hp _
      _ = τ.functional (star x * x * p) := τ.tracial _ _
  have h2 : star x * p * (p * x) = star x * p * x := by
    simp only [mul_assoc, ← mul_assoc p p, hpp]
  have h3 : τ.functional (star x * p * (x * p)) =
      τ.functional (p * star x * p * x) := by
    simpa only [mul_assoc] using τ.tracial (star x * p * x) p
  simp only [star_sub, star_mul, hsp, sub_mul, mul_sub, map_sub, h1, h2, h3]
  simp only [← mul_assoc]
  ring

lemma trace_cross_compression_square (τ : TracialState D) {p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (x : D) :
    τ.functional (star (q * x * p) * (q * x * p)) =
      τ.functional (p * star x * q * x) := by
  have hsp : star p = p := hp.isSelfAdjoint
  have hsq : star q = q := hq.isSelfAdjoint
  have hqq : q * q = q := hq.isIdempotentElem
  calc
    τ.functional (star (q * x * p) * (q * x * p)) =
        τ.functional (p * (star x * q * x) * p) := by
      simp only [star_mul, hsp, hsq, mul_assoc, ← mul_assoc q q, hqq]
    _ = τ.functional (p * (star x * q * x)) := trace_projection_corner τ hp _
    _ = τ.functional (p * star x * q * x) := by simp only [mul_assoc]

variable [StarOrderedRing D]

lemma orthogonal_pair_energy_identity (τ : TracialState D) {p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) (x : D) :
    traceTwoNorm τ (x * (p + q) - (p + q) * x) ^ 2 =
      traceTwoNorm τ (x * p - p * x) ^ 2 + traceTwoNorm τ (x * q - q * x) ^ 2 -
        2 * traceTwoNorm τ (q * x * p) ^ 2 - 2 * traceTwoNorm τ (p * x * q) ^ 2 := by
  have hid : τ.functional (star (x * (p + q) - (p + q) * x) *
      (x * (p + q) - (p + q) * x)) =
      τ.functional (star (x * p - p * x) * (x * p - p * x)) +
      τ.functional (star (x * q - q * x) * (x * q - q * x)) -
      2 * τ.functional (star (q * x * p) * (q * x * p)) -
      2 * τ.functional (star (p * x * q) * (p * x * q)) := by
    rw [trace_commutator_square_expansion τ (hp.add hq hpq),
      trace_commutator_square_expansion τ hp, trace_commutator_square_expansion τ hq,
      trace_cross_compression_square τ hp hq, trace_cross_compression_square τ hq hp]
    simp only [mul_add, add_mul, map_add]
    ring
  simpa [traceTwoNorm_sq] using congrArg Complex.re hid

lemma orthogonal_pair_energy_le (τ : TracialState D) {p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) (x : D) :
    traceTwoNorm τ (x * (p + q) - (p + q) * x) ^ 2 ≤
      traceTwoNorm τ (x * p - p * x) ^ 2 + traceTwoNorm τ (x * q - q * x) ^ 2 := by
  rw [orthogonal_pair_energy_identity τ hp hq hpq]
  nlinarith [sq_nonneg (traceTwoNorm τ (q * x * p)),
    sq_nonneg (traceTwoNorm τ (p * x * q))]

theorem orthogonal_sum_energy_le {I : Type uI} (s : Finset I) (t : I → D)
    (ht : ∀ i ∈ s, IsStarProjection (t i))
    (hortho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0)
    (τ : TracialState D) (x : D) :
    IsStarProjection (∑ i ∈ s, t i) ∧
      traceTwoNorm τ (x * (∑ i ∈ s, t i) - (∑ i ∈ s, t i) * x) ^ 2 ≤
        ∑ i ∈ s, traceTwoNorm τ (x * t i - t i * x) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsStarProjection.zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, IsStarProjection (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hso : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0 :=
      fun i hi j hj hij => hortho i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij
    obtain ⟨hproj, henergy⟩ := ih hs hso
    have ha0 : t a * ∑ i ∈ s, t i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact hortho a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    have hap := ht a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha]
    refine ⟨hap.add hproj ha0, ?_⟩
    rw [Finset.sum_insert ha]
    exact (orthogonal_pair_energy_le τ hap hproj ha0 x).trans (add_le_add (le_refl _) henergy)

end OrthogonalEnergy

section WeightedAveraging

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype I]

lemma weightedAverage_nonneg (w : I → ℝ) (v : I → D)
    (hw : ∀ i, 0 ≤ w i) {b : D} (hb : 0 ≤ b) :
    0 ≤ weightedAverage w v b := by
  exact Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (star_right_conjugate_nonneg hb (v i))

end WeightedAveraging

section ProjectiveAveraging

open scoped TensorProduct

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_projection_sq (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) : traceTwoNorm τ q ^ 2 = (τ.functional q).re := by
  rw [traceTwoNorm_sq, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem]

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

omit [StarOrderedRing D] in
lemma coe_nonneg_iff (a : ProjectionCorner hp) : 0 ≤ (a : D) ↔ 0 ≤ a := Iff.rfl

lemma compress_nonneg {a : D} (ha : 0 ≤ a) : 0 ≤ compress hp a := by
  rw [← coe_nonneg_iff]
  exact hp.isSelfAdjoint.conjugate_nonneg ha

end ProjectionCorner

end ProjectionOrder

section SpectralThresholds

variable {D : Type uD} [CStarAlgebra D]

lemma spectralThreshold_projection {a : D} (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    IsStarProjection (spectralThreshold a t) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc _ a * cfc _ a = cfc _ a
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma spectralThreshold_complement {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    1 - spectralThreshold a t = cfc (fun s : ℝ => if t ≤ s then (0 : ℝ) else 1) a := by
  rw [spectralThreshold, ← cfc_one ℝ a ha,
    ← cfc_sub _ _ a (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

variable [PartialOrder D] [StarOrderedRing D]

lemma spectralThreshold_lower {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    t • spectralThreshold a t ≤ spectralThreshold a t * a * spectralThreshold a t := by
  unfold spectralThreshold
  nth_rw 3 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_smul _ _ a (hf.continuousOn _)]
  apply (cfc_le_iff _ _ a (hf.continuousOn _) (hf.continuousOn _) ha).mpr
  intro x _
  simp only [smul_eq_mul]
  split_ifs with hx
  · simpa using hx
  · simp

lemma spectralThreshold_complement_upper {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    (1 - spectralThreshold a t) * a * (1 - spectralThreshold a t) ≤
      t • (1 - spectralThreshold a t) := by
  rw [spectralThreshold_complement ha hf]
  nth_rw 2 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_smul _ _ a (hf.continuousOn _)]
  apply (cfc_le_iff _ _ a (hf.continuousOn _) (hf.continuousOn _) ha).mpr
  intro x _
  simp only [smul_eq_mul]
  split_ifs with hx
  · simp
  · simpa using (le_of_lt (lt_of_not_ge hx))

lemma compress_perturbation_lower {a b p : D} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hp : IsStarProjection p) :
    p * a * p - ‖a - b‖ • p ≤ p * b * p := by
  have h := star_left_conjugate_le_conjugate (ha.sub hb).le_algebraMap_norm_self p
  simp only [hp.isSelfAdjoint.star_eq, mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, smul_mul_assoc, mul_one, hp.isIdempotentElem.eq] at h
  exact sub_le_comm.mp h

lemma compress_perturbation_upper {a b p : D} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hp : IsStarProjection p) :
    p * b * p ≤ p * a * p + ‖a - b‖ • p := by
  have h := compress_perturbation_lower hb ha hp
  rw [norm_sub_rev] at h
  exact sub_le_iff_le_add.mp h

end SpectralThresholds

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

section FullProjectionFrames

open Filter Topology

open scoped CStarAlgebra

variable {A : Type uA} [CStarAlgebra A]

theorem exists_finite_fullness_approximation {e : A} (he : IsFull e) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (A × A), ‖1 - (l.map fun v => v.1 * e * v.2).sum‖ < ε := by
  have h : (1 : A) ∈ closure (finiteSandwichIdeal e : Set A) := by
    have hs : TwoSidedIdeal.span {e} ≤ finiteSandwichIdeal e := by
      apply TwoSidedIdeal.span_le.mpr
      intro a ha
      have haeq := Set.mem_singleton_iff.mp ha
      subst a
      exact (mem_finiteSandwichIdeal e e).mpr ⟨[(1, 1)], by simp⟩
    apply closure_mono (show (TwoSidedIdeal.span {e} : Set A) ⊆
      (finiteSandwichIdeal e : Set A) from hs)
    rw [he]
    trivial
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨l, rfl⟩ := (mem_finiteSandwichIdeal e s).mp hs
  exact ⟨l, by simpa only [dist_eq_norm] using hdist⟩

theorem exists_finite_fullness_identity {e : A} (he : IsFull e) :
    ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = 1 := by
  obtain ⟨l, hl⟩ := exists_finite_fullness_approximation he (ε := 1) zero_lt_one
  let s := (l.map fun v => v.1 * e * v.2).sum
  have hs : s ∈ finiteSandwichIdeal e := (mem_finiteSandwichIdeal e s).mpr ⟨l, rfl⟩
  have hu : IsUnit s := by
    have := (Units.oneSub (1 - s) hl).isUnit
    change IsUnit (1 - (1 - s)) at this
    simpa only [sub_sub_cancel] using this
  obtain ⟨u, hu⟩ := hu
  have hone := (finiteSandwichIdeal e).mul_mem_left (↑(u⁻¹) : A) s hs
  rw [← hu, Units.inv_mul] at hone
  exact (mem_finiteSandwichIdeal e 1).mp hone

variable [PartialOrder A] [StarOrderedRing A]

lemma star_add_mul_add_le (a b : A) :
    star (a + b) * (a + b) ≤ (2 : ℝ) • (star a * a + star b * b) := by
  have h := star_mul_self_nonneg (a - b)
  rw [← sub_nonneg]
  convert h using 1
  simp only [star_add, star_sub, two_smul]
  noncomm_ring

lemma list_square_sum_nonneg (l : List (A × A)) :
    0 ≤ (l.map fun v => star v.2 * v.2).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simpa using add_nonneg (star_mul_self_nonneg v.2) ih

lemma finite_product_sum_bound (l : List (A × A)) :
    ∃ C : ℝ, 0 < C ∧
      star (l.map fun v => v.1 * v.2).sum * (l.map fun v => v.1 * v.2).sum ≤
        C • (l.map fun v => star v.2 * v.2).sum := by
  induction l with
  | nil => exact ⟨1, zero_lt_one, by simp⟩
  | cons v l ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let K := ‖star v.1 * v.1‖ + C
    have hK : 0 < K := add_pos_of_nonneg_of_pos (norm_nonneg _) hC
    have hsingle : star (v.1 * v.2) * (v.1 * v.2) ≤
        ‖star v.1 * v.1‖ • (star v.2 * v.2) := by
      simpa only [star_mul, mul_assoc] using
        (CStarAlgebra.star_left_conjugate_le_norm_smul
          (a := v.2) (b := star v.1 * v.1))
    refine ⟨2 * K, mul_pos (by norm_num) hK, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ (2 : ℝ) • (star (v.1 * v.2) * (v.1 * v.2) +
          star (l.map fun v => v.1 * v.2).sum * (l.map fun v => v.1 * v.2).sum) :=
        star_add_mul_add_le _ _
      _ ≤ (2 : ℝ) • (‖star v.1 * v.1‖ • (star v.2 * v.2) +
          C • (l.map fun v => star v.2 * v.2).sum) :=
        smul_le_smul_of_nonneg_left (add_le_add hsingle hbound) (by norm_num)
      _ ≤ (2 : ℝ) • (K • (star v.2 * v.2) +
          K • (l.map fun v => star v.2 * v.2).sum) := by
        apply smul_le_smul_of_nonneg_left _ (by norm_num)
        exact add_le_add
          (smul_le_smul_of_nonneg_right (by dsimp [K]; linarith) (star_mul_self_nonneg _))
          (smul_le_smul_of_nonneg_right (by dsimp [K]; linarith [norm_nonneg (star v.1 * v.1)])
            (list_square_sum_nonneg l))
      _ = _ := by rw [← smul_add, mul_smul]

theorem finite_gram_isUnit (l : List (A × A))
    (h : (l.map fun v => v.1 * v.2).sum = 1) :
    IsUnit (l.map fun v => star v.2 * v.2).sum := by
  obtain ⟨C, hC, hb⟩ := finite_product_sum_bound l
  rw [h, star_one, one_mul] at hb
  have hy : IsUnit (C • (l.map fun v => star v.2 * v.2).sum) :=
    CStarAlgebra.isUnit_of_le 1 hb
  have hs : IsUnit (algebraMap ℝ A C) := (isUnit_iff_ne_zero.mpr hC.ne').map _
  rw [Algebra.smul_def] at hy
  exact (hs.mul_left_iff).mp hy

theorem exists_positive_fullness_frame
    {e : A} (he : 0 ≤ e) (hfull : IsFull e) :
    ∃ x : List A, (x.map fun v => star v * e * v).sum = 1 := by
  obtain ⟨l, hl⟩ := exists_finite_fullness_identity hfull
  let t := CFC.sqrt e
  have ht : IsSelfAdjoint t := .of_nonneg (CFC.sqrt_nonneg e)
  have ht2 : t * t = e := CFC.sqrt_mul_sqrt_self e
  let w : List (A × A) := l.map fun v => (v.1 * t, t * v.2)
  have hw : (w.map fun v => v.1 * v.2).sum = 1 := by
    simpa only [w, List.map_map, Function.comp_def, mul_assoc, ← mul_assoc t t, ht2] using hl
  let y := (w.map fun v => star v.2 * v.2).sum
  have hy : IsStrictlyPositive y :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨list_square_sum_nonneg w, finite_gram_isUnit w hw⟩
  let z := CFC.rpow y (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hzyz : z * y * z = 1 := CFC.conjugate_rpow_neg_one_half y hy
  refine ⟨l.map (fun v => v.2 * z), ?_⟩
  have hysum : y = (l.map fun v => star v.2 * e * v.2).sum := by
    simp only [y, w, List.map_map, Function.comp_def, star_mul, ht.star_eq,
      mul_assoc, ← mul_assoc t t, ht2]
  rw [hysum] at hzyz
  rw [List.map_map]
  convert hzyz using 1
  have hdist (m : List (A × A)) :
      (m.map fun v => star (v.2 * z) * e * (v.2 * z)).sum =
        z * (m.map fun v => star v.2 * e * v.2).sum * z := by
    induction m with
    | nil => simp
    | cons v m ih =>
      simp only [List.map_cons, List.sum_cons, star_mul, hz.star_eq, mul_add, add_mul]
      simpa only [mul_assoc, star_mul, hz.star_eq] using
        congrArg (fun a => z * star v.2 * e * v.2 * z + a) ih
  exact hdist l

end FullProjectionFrames

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

lemma ProjectionSubequivalent.refl (e : D) (he : IsStarProjection e) :
    ProjectionSubequivalent e e :=
  ⟨e, by rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem], he.isIdempotentElem⟩

lemma ProjectionSubequivalent.trans {e f g : D}
    (h₁ : ProjectionSubequivalent e f)
    (h₂ : ProjectionSubequivalent f g) : ProjectionSubequivalent e g := by
  obtain ⟨v, hv, hfv⟩ := h₁
  obtain ⟨w, hw, hgw⟩ := h₂
  refine ⟨w * v, ?_, ?_⟩
  · simp only [star_mul]
    calc
      star v * star w * (w * v) = star v * (star w * w) * v := by simp only [mul_assoc]
      _ = e := by rw [hw, mul_assoc, hfv, hv]
  · rw [← mul_assoc, hgw]

variable [PartialOrder D] [StarOrderedRing D]

lemma ProjectionSubequivalent.of_le {e g : D} (he : IsStarProjection e)
    (hg : IsStarProjection g) (h : e ≤ g) : ProjectionSubequivalent e g :=
  ⟨e, by rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem],
    (he.le_iff_mul_eq_right hg).mp h⟩

lemma ProjectionSubequivalent.final_projection {e g : D} (he : IsStarProjection e)
    (hg : IsStarProjection g) (h : ProjectionSubequivalent e g) :
    ∃ v : D, star v * v = e ∧ IsStarProjection (v * star v) ∧ v * star v ≤ g := by
  obtain ⟨v, hv, hgv⟩ := h
  have hf : IsStarProjection (v * star v) :=
    ⟨isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star.mp
      (hv ▸ he.isIdempotentElem), by simp only [IsSelfAdjoint, star_mul, star_star]⟩
  exact ⟨v, hv, hf, (hf.le_iff_mul_eq_right hg).mpr (by rw [← mul_assoc, hgv])⟩

lemma ProjectionSubequivalent.trace_le (τ : TracialState D) {e g : D}
    (he : IsStarProjection e) (hg : IsStarProjection g)
    (h : ProjectionSubequivalent e g) : (τ.functional e).re ≤ (τ.functional g).re := by
  obtain ⟨v, hv, _, hle⟩ := h.final_projection he hg
  have h := τ.functional.monotone hle
  rw [← hv, τ.tracial (star v) v]
  exact (Complex.le_def.mp h).1

lemma exists_corner_normalizer {p a : D} (hp : IsStarProjection p) (ha : 0 ≤ a)
    {c : ℝ} (hc : 0 < c) (hbound : c • p ≤ p * a * p) :
    ∃ z : ProjectionCorner hp, IsSelfAdjoint z ∧
      (z : D) * a * (z : D) = p := by
  let b := ProjectionCorner.compress hp a
  have hb : 0 ≤ b := ProjectionCorner.compress_nonneg hp ha
  have hcpos : IsStrictlyPositive (c • (1 : ProjectionCorner hp)) := by
    apply IsStrictlyPositive.iff_of_unital.mpr
    refine ⟨smul_nonneg hc.le zero_le_one, ?_⟩
    rw [Algebra.smul_def, mul_one]
    exact (isUnit_iff_ne_zero.mpr hc.ne').map (algebraMap ℝ (ProjectionCorner hp))
  have hbpos : IsStrictlyPositive b := hcpos.of_le hbound
  let z := CFC.rpow b (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hzbz : z * b * z = 1 := CFC.conjugate_rpow_neg_one_half b hbpos
  refine ⟨z, hz, ?_⟩
  have h := congrArg (fun x : ProjectionCorner hp => (x : D)) hzbz
  change (z : D) * (p * a * p) * (z : D) = p at h
  simp only [← mul_assoc] at h
  rw [z.property.2] at h
  simpa only [mul_assoc, z.property.1] using h

lemma projectionSubequivalent_of_compression {e g v : D}
    (he : IsStarProjection e) (hgv : g * v = v)
    {c : ℝ} (hc : 0 < c) (hbound : c • e ≤ e * (star v * v) * e) :
    ProjectionSubequivalent e g := by
  obtain ⟨z, hz, hnorm⟩ := exists_corner_normalizer he (star_mul_self_nonneg v) hc hbound
  refine ⟨v * (z : D), ?_, by rw [← mul_assoc, hgv]⟩
  rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe he hz).star_eq]
  simpa only [mul_assoc] using hnorm

lemma exists_spectral_cut (hRR : RealRankZero D) {a : D} (ha : IsSelfAdjoint a)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧
      (t - ε) • e ≤ e * a * e ∧
      (1 - e) * a * (1 - e) ≤ (t + ε) • (1 - e) := by
  obtain ⟨b, hb, hbf, hba⟩ := hRR a ha ε hε
  have hbf' := realSpectrum_finite hb hbf
  let e := spectralThreshold b t
  have he : IsStarProjection e := spectralThreshold_projection hbf' t
  have hr : IsStarProjection (1 - e) := he.one_sub
  have hn : ‖b - a‖ ≤ ε := (norm_sub_rev b a ▸ hba.le)
  refine ⟨e, he, ?_, ?_⟩
  · calc
      (t - ε) • e = t • e - ε • e := sub_smul _ _ _
      _ ≤ e * b * e - ‖b - a‖ • e := sub_le_sub
        (spectralThreshold_lower hb hbf' t)
        (smul_le_smul_of_nonneg_right hn he.nonneg)
      _ ≤ e * a * e := compress_perturbation_lower hb ha he
  · calc
      (1 - e) * a * (1 - e) ≤ (1 - e) * b * (1 - e) + ‖b - a‖ • (1 - e) :=
        compress_perturbation_upper hb ha hr
      _ ≤ t • (1 - e) + ε • (1 - e) := add_le_add
        (spectralThreshold_complement_upper hb hbf' t)
        (smul_le_smul_of_nonneg_right hn hr.nonneg)
      _ = (t + ε) • (1 - e) := (add_smul _ _ _).symm

omit [PartialOrder D] [StarOrderedRing D] in
lemma ProjectionCorner.coe_mul_compress_mul {p : D} (hp : IsStarProjection p)
    (x y : ProjectionCorner hp) (a : D) :
    ((x * compress hp a * y : ProjectionCorner hp) : D) = (x : D) * a * (y : D) := by
  change (x : D) * (p * a * p) * (y : D) = _
  simp only [← mul_assoc]
  rw [x.property.2]
  simp only [mul_assoc, y.property.1]

lemma exists_column_cut (hRR : RealRankZero D) {f a : D} (hf : IsStarProjection f)
    (ha : IsSelfAdjoint a) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧
      (3 / 8 : ℝ) • e ≤ e * a * e ∧
      (f - e) * a * (f - e) ≤ (5 / 8 : ℝ) • (f - e) := by
  let b := ProjectionCorner.compress hf a
  have hb : IsSelfAdjoint b := by
    apply Subtype.ext
    change star (f * a * f) = f * a * f
    simpa only [hf.isSelfAdjoint.star_eq] using (ha.conjugate f).star_eq
  obtain ⟨e, he, hlow, hupp⟩ := exists_spectral_cut (realRankZero_corner hRR hf) hb
    (1 / 2) (ε := 1 / 8) (by norm_num)
  have he' : IsStarProjection (e : D) := he.map (ProjectionCorner.inclusion hf)
  refine ⟨(e : D), he', (he'.le_iff_mul_eq_right hf).mpr e.property.1, ?_, ?_⟩
  · norm_num only [show (1 / 2 - 1 / 8 : ℝ) = 3 / 8 by norm_num] at hlow
    have h : (3 / 8 : ℝ) • (e : D) ≤ ((e * b * e : ProjectionCorner hf) : D) := hlow
    rwa [ProjectionCorner.coe_mul_compress_mul] at h
  · norm_num only [show (1 / 2 + 1 / 8 : ℝ) = 5 / 8 by norm_num] at hupp
    have h : (((1 - e) * b * (1 - e) : ProjectionCorner hf) : D) ≤
        (5 / 8 : ℝ) • (f - (e : D)) := hupp
    rwa [ProjectionCorner.coe_mul_compress_mul] at h

theorem split_column (hRR : RealRankZero D) (n : ℕ) {f : D}
    (hf : IsStarProjection f) (g v : Fin n → D)
    (hg : ∀ i, IsStarProjection (g i))
    (hleft : ∀ i, g i * v i = v i) (hsum : ∑ i, star (v i) * v i = f) :
    ∃ e : Fin n → D, (∀ i, IsStarProjection (e i)) ∧
      Pairwise (fun i j => e i * e j = 0) ∧
      (∑ i, e i = f) ∧ ∀ i, ProjectionSubequivalent (e i) (g i) := by
  induction n generalizing f with
  | zero =>
    have hf0 : f = 0 := by simpa using hsum.symm
    refine ⟨Fin.elim0, (fun i => Fin.elim0 i), ?_, ?_, (fun i => Fin.elim0 i)⟩
    · intro i; exact Fin.elim0 i
    · simp [hf0]
  | succ n ih =>
    let a := star (v 0) * v 0
    have ha : IsSelfAdjoint a := (star_mul_self_nonneg (v 0)).isSelfAdjoint
    obtain ⟨e, he, hef, hlow, hupp⟩ := exists_column_cut hRR hf ha
    let r := f - e
    have hr : IsStarProjection r := (he.le_iff_sub hf).mp hef
    have hef' : e * f = e := (he.le_iff_mul_eq_left hf).mp hef
    have hfe : f * e = e := (he.le_iff_mul_eq_right hf).mp hef
    have hrf : r * f = r := by simp only [r, sub_mul, hf.isIdempotentElem.eq, hef']
    have her : e * r = 0 := by simp only [r, mul_sub, hef', he.isIdempotentElem.eq, sub_self]
    have hre : r * e = 0 := by simp only [r, sub_mul, hfe, he.isIdempotentElem.eq, sub_self]
    have hecomp : ProjectionSubequivalent e (g 0) :=
      projectionSubequivalent_of_compression he (hleft 0) (by norm_num : (0 : ℝ) < 3 / 8) hlow
    let q := ∑ i : Fin n, star (v i.succ) * v i.succ
    have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
    have hqeq : a + q = f := by simpa only [Fin.sum_univ_succ] using hsum
    have hrq : r * q * r = r - r * a * r := by
      calc
        r * q * r = r * f * r - r * a * r := by rw [← hqeq]; noncomm_ring
        _ = r - r * a * r := by rw [hrf, hr.isIdempotentElem]
    have hbound : (3 / 8 : ℝ) • r ≤ r * q * r := by
      calc
        (3 / 8 : ℝ) • r = r - (5 / 8 : ℝ) • r := by
          calc
            (3 / 8 : ℝ) • r = (1 - 5 / 8 : ℝ) • r := by norm_num
            _ = r - (5 / 8 : ℝ) • r := by rw [sub_smul, one_smul]
        _ ≤ r - r * a * r := sub_le_sub_left hupp r
        _ = r * q * r := hrq.symm
    obtain ⟨z, hz, hnorm⟩ := exists_corner_normalizer hr hq
      (by norm_num : (0 : ℝ) < 3 / 8) hbound
    let w : Fin n → D := fun i => v i.succ * (z : D)
    have hwleft (i : Fin n) : g i.succ * w i = w i := by
      dsimp [w]; rw [← mul_assoc, hleft]
    have hzstar : star (z : D) = (z : D) := (ProjectionCorner.isSelfAdjoint_coe hr hz).star_eq
    have hwsum : ∑ i : Fin n, star (w i) * w i = r := by
      calc
        _ = (z : D) * q * (z : D) := by
          simp only [w, q, star_mul, hzstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = r := hnorm
    obtain ⟨E, hE, hEorth, hEsum, hEcomp⟩ := ih hr (fun i => g i.succ) w
      (fun i => hg i.succ) hwleft hwsum
    have hEr (i : Fin n) : E i ≤ r := by
      rw [← hEsum]
      exact Finset.single_le_sum (fun j _ => (hE j).nonneg) (Finset.mem_univ i)
    have hEright (i : Fin n) : E i * r = E i := ((hE i).le_iff_mul_eq_left hr).mp (hEr i)
    have hEleft (i : Fin n) : r * E i = E i := ((hE i).le_iff_mul_eq_right hr).mp (hEr i)
    refine ⟨Fin.cases e E, ?_, ?_, ?_, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact he
      | succ i => exact hE i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          change e * E j = 0
          rw [← hEleft j, ← mul_assoc, her, zero_mul]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          change E i * e = 0
          rw [← hEright i, mul_assoc, hre, mul_zero]
        | succ j =>
          exact hEorth (fun h => hij (congrArg Fin.succ h))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, hEsum]
      dsimp [r]; abel
    · intro i; cases i using Fin.cases with
      | zero => exact hecomp
      | succ i => exact hEcomp i

end ColumnSplitting

section ProjectionRefinement

variable {D : Type uD} [CStarAlgebra D]

lemma mul_eq_zero_of_supports {a b p q : D} (ha : a * p = a)
    (hb : q * b = b) (hpq : p * q = 0) : a * b = 0 := by
  calc
    a * b = (a * p) * (q * b) := by rw [ha, hb]
    _ = a * (p * q) * b := by simp only [mul_assoc]
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

lemma projection_mul_zero_symm {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : p * q = 0) : q * p = 0 := by
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, star_zero]
    using congrArg star h

lemma ProjectionSubequivalent.range {e v : D} (he : IsStarProjection e)
    (hv : star v * v = e) :
    ProjectionSubequivalent e (v * star v) ∧ ProjectionSubequivalent (v * star v) e := by
  have hve : v * e = v := partialIsometry_right_support he hv
  refine ⟨⟨v, hv, ?_⟩, ⟨star v, by simp only [star_star], ?_⟩⟩
  · rw [mul_assoc, hv, hve]
  · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star hve

lemma ProjectionSubequivalent.orthogonal_add {e f p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0)
    (he : ProjectionSubequivalent e p) (hf : ProjectionSubequivalent f q) :
    ProjectionSubequivalent (e + f) (p + q) := by
  obtain ⟨v, hv, hpv⟩ := he
  obtain ⟨w, hw, hqw⟩ := hf
  have hqp := projection_mul_zero_symm hp hq hpq
  have hvp : star v * p = star v := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hwq : star w * q = star w := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hqw
  have hvw : star v * w = 0 := mul_eq_zero_of_supports hvp hqw hpq
  have hwv : star w * v = 0 := mul_eq_zero_of_supports hwq hpv hqp
  have hpw : p * w = 0 := mul_eq_zero_of_supports hp.isIdempotentElem hqw hpq
  have hqv : q * v = 0 := mul_eq_zero_of_supports hq.isIdempotentElem hpv hqp
  exact ⟨v + w, by simp only [star_add, add_mul, mul_add, hv, hw, hvw, hwv, add_zero,
    zero_add], by simp only [add_mul, mul_add, hpv, hqw, hpw, hqv, add_zero, zero_add]⟩

variable [PartialOrder D] [StarOrderedRing D]

lemma comparison_pair (hRR : RealRankZero D) {x y h : D}
    (hx : IsStarProjection x) (hy : IsStarProjection y) (hh : IsStarProjection h)
    (hxy : x * y = 0) (hxh : ProjectionSubequivalent x h)
    (hyh : ProjectionSubequivalent y h) :
    ∃ k z : D, IsStarProjection k ∧ IsStarProjection z ∧ k + z = x + y ∧
      x ≤ z ∧ ProjectionSubequivalent k z ∧ ProjectionSubequivalent z h := by
  obtain ⟨w, hw, hwproj, hwle⟩ := hxh.final_projection hx hh
  obtain ⟨u, hu, hhu⟩ := hyh
  let p := w * star w
  have hp : IsStarProjection p := hwproj
  have hq : IsStarProjection (h - p) := (hp.le_iff_sub hh).mp hwle
  have hpq : p * (h - p) = 0 := by
    rw [mul_sub, (hp.le_iff_mul_eq_left hh).mp hwle, hp.isIdempotentElem, sub_self]
  let targets : Fin 2 → D := ![p, h - p]
  let v : Fin 2 → D := ![p * u, (h - p) * u]
  have ht (i : Fin 2) : IsStarProjection (targets i) := by
    fin_cases i
    · exact hp
    · exact hq
  have hvleft (i : Fin 2) : targets i * v i = v i := by
    fin_cases i
    · change p * (p * u) = p * u
      rw [← mul_assoc, hp.isIdempotentElem]
    · change (h - p) * ((h - p) * u) = (h - p) * u
      rw [← mul_assoc, hq.isIdempotentElem]
  have hvsum : ∑ i, star (v i) * v i = y := by
    rw [Fin.sum_univ_two]
    change star (p * u) * (p * u) + star ((h - p) * u) * ((h - p) * u) = y
    simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    calc
      _ = star u * p * u + star u * (h - p) * u := by
        simp only [mul_assoc, ← mul_assoc p p, hp.isIdempotentElem.eq,
          ← mul_assoc (h - p) (h - p), hq.isIdempotentElem.eq]
      _ = star u * h * u := by noncomm_ring
      _ = y := by rw [mul_assoc, hhu, hu]
  obtain ⟨E, hE, hEorth, hEsum, hEcomp⟩ := split_column hRR 2 hy targets v ht hvleft hvsum
  have hsum : E 0 + E 1 = y := by simpa only [Fin.sum_univ_two] using hEsum
  have h01 : E 0 * E 1 = 0 := hEorth (by decide : (0 : Fin 2) ≠ 1)
  have hE0y : E 0 ≤ y := by rw [← hsum]; exact le_add_of_nonneg_right (hE 1).nonneg
  have hE1y : E 1 ≤ y := by rw [← hsum]; exact le_add_of_nonneg_left (hE 0).nonneg
  have hx1 : x * E 1 = 0 := mul_eq_zero_of_supports hx.isIdempotentElem
    (((hE 1).le_iff_mul_eq_right hy).mp hE1y) hxy
  have hx0 : x * E 0 = 0 := mul_eq_zero_of_supports hx.isIdempotentElem
    (((hE 0).le_iff_mul_eq_right hy).mp hE0y) hxy
  have hz : IsStarProjection (x + E 1) := hx.add (hE 1) hx1
  have hxz : x ≤ x + E 1 := le_add_of_nonneg_right (hE 1).nonneg
  have h0xcomp : ProjectionSubequivalent (E 0) x :=
    (hEcomp 0).trans (ProjectionSubequivalent.range hx hw).2
  have hzcomp : ProjectionSubequivalent (x + E 1) h := by
    have hc := ProjectionSubequivalent.orthogonal_add hp hq hpq
      (ProjectionSubequivalent.range hx hw).1 (hEcomp 1)
    simpa only [add_sub_cancel] using hc
  refine ⟨E 0, x + E 1, hE 0, hz, ?_, hxz,
    h0xcomp.trans (ProjectionSubequivalent.of_le hx hz hxz), hzcomp⟩
  rw [← hsum]
  abel

end ProjectionRefinement

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

section ProjectionSorting

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma projection_family_orthogonal {I : Type uI} [Fintype I] {f : D}
    (hf : IsStarProjection f) (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (hsum : ∑ i, e i = f) : Pairwise (fun i j => e i * e j = 0) := by
  classical
  intro i j hij
  have hif : e i ≤ f := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => (he k).nonneg) (Finset.mem_univ i)
  have hr : IsStarProjection (f - e i) := ((he i).le_iff_sub hf).mp hif
  have hrest : ∑ k ∈ Finset.univ.erase i, e k = f - e i := by
    rw [← hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
  have hjr : e j ≤ f - e i := by
    rw [← hrest]
    exact Finset.single_le_sum (fun k _ => (he k).nonneg)
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  have hir : e i * (f - e i) = 0 := by
    rw [mul_sub, ((he i).le_iff_mul_eq_left hf).mp hif, (he i).isIdempotentElem, sub_self]
  exact mul_eq_zero_of_supports (he i).isIdempotentElem
    (((he j).le_iff_mul_eq_right hr).mp hjr) hir

lemma collect_max_piece (hRR : RealRankZero D) (n : ℕ) {x f g : D}
    (hx : IsStarProjection x) (hf : IsStarProjection f) (hg : IsStarProjection g)
    (v : Fin n → D) (hv : ∀ i, IsStarProjection (v i))
    (hsum : x + ∑ i, v i = f) (hxg : ProjectionSubequivalent x g)
    (hvg : ∀ i, ProjectionSubequivalent (v i) g) :
    ∃ p : D, ∃ E : Fin n → D, IsStarProjection p ∧
      (∀ i, IsStarProjection (E i)) ∧ p + ∑ i, E i = f ∧
      x ≤ p ∧ ProjectionSubequivalent p g ∧
      ∀ i, ProjectionSubequivalent (E i) p := by
  induction n generalizing x f with
  | zero =>
    refine ⟨x, Fin.elim0, hx, (fun i => Fin.elim0 i), ?_, le_rfl, hxg,
      (fun i => Fin.elim0 i)⟩
    simpa only [Fin.sum_univ_zero] using hsum
  | succ n ih =>
    have htail : 0 ≤ ∑ i : Fin n, v i.succ := Finset.sum_nonneg fun i _ => (hv _).nonneg
    have hxf : x ≤ f := by
      rw [← hsum]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hv i).nonneg)
    have hrest : IsStarProjection (f - x) := (hx.le_iff_sub hf).mp hxf
    have hv0rest : v 0 ≤ f - x := by
      have heq : f - x = v 0 + ∑ i : Fin n, v i.succ := by
        rw [← hsum, Fin.sum_univ_succ]; abel
      rw [heq]
      exact le_add_of_nonneg_right htail
    have hxrest : x * (f - x) = 0 := by
      rw [mul_sub, (hx.le_iff_mul_eq_left hf).mp hxf, hx.isIdempotentElem, sub_self]
    have hxv : x * v 0 = 0 := mul_eq_zero_of_supports hx.isIdempotentElem
      (((hv 0).le_iff_mul_eq_right hrest).mp hv0rest) hxrest
    obtain ⟨k, z, hk, hz, hkz, hxz, hkzcomp, hzg⟩ :=
      comparison_pair hRR hx (hv 0) hg hxv hxg (hvg 0)
    have hnewsum : k + (z + ∑ i : Fin n, v i.succ) = f := by
      rw [← add_assoc, hkz]
      simpa only [Fin.sum_univ_succ, add_assoc] using hsum
    have hkf : k ≤ f := by
      rw [← hnewsum]
      exact le_add_of_nonneg_right (add_nonneg hz.nonneg htail)
    have hf' : IsStarProjection (f - k) := (hk.le_iff_sub hf).mp hkf
    have hzsum : z + ∑ i : Fin n, v i.succ = f - k := by rw [← hnewsum]; abel
    obtain ⟨p, E, hp, hE, hpEsum, hzp, hpg, hEp⟩ :=
      ih hz hf' (fun i => v i.succ) (fun i => hv i.succ) hzsum hzg (fun i => hvg i.succ)
    refine ⟨p, Fin.cases k E, hp, ?_, ?_, hxz.trans hzp, hpg, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact hk
      | succ i => exact hE i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      calc
        p + (k + ∑ i, E i) = k + (p + ∑ i, E i) := by abel
        _ = f := by rw [hpEsum]; abel
    · intro i; cases i using Fin.cases with
      | zero => exact hkzcomp.trans (ProjectionSubequivalent.of_le hz hp hzp)
      | succ i => exact hEp i

theorem comparison_sorted_partition (hRR : RealRankZero D) (n : ℕ) {f g : D}
    (hf : IsStarProjection f) (hg : IsStarProjection g)
    (v : Fin n → D) (hv : ∀ i, IsStarProjection (v i))
    (hsum : ∑ i, v i = f) (hvg : ∀ i, ProjectionSubequivalent (v i) g) :
    ∃ e : Fin n → D, (∀ i, IsStarProjection (e i)) ∧ (∑ i, e i = f) ∧
      (∀ i j, i ≤ j → ProjectionSubequivalent (e j) (e i)) ∧
      ∀ i, ProjectionSubequivalent (e i) g := by
  induction n generalizing f g with
  | zero =>
    refine ⟨Fin.elim0, (fun i => Fin.elim0 i), ?_, ?_, (fun i => Fin.elim0 i)⟩
    · simpa only [Fin.sum_univ_zero] using hsum
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    have hsum' : v 0 + ∑ i : Fin n, v i.succ = f := by
      simpa only [Fin.sum_univ_succ] using hsum
    obtain ⟨p, E, hp, hE, hpE, _, hpg, hEp⟩ := collect_max_piece hRR n (hv 0) hf hg
      (fun i => v i.succ) (fun i => hv i.succ) hsum' (hvg 0) (fun i => hvg i.succ)
    have hpf : p ≤ f := by
      rw [← hpE]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hE i).nonneg)
    have hr : IsStarProjection (f - p) := (hp.le_iff_sub hf).mp hpf
    have hEsum : ∑ i, E i = f - p := by rw [← hpE]; abel
    obtain ⟨s, hs, hssum, hsort, hsp⟩ := ih hr hp E hE hEsum hEp
    refine ⟨Fin.cases p s, ?_, ?_, ?_, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact hp
      | succ i => exact hs i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, hssum]
      abel
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact ProjectionSubequivalent.refl p hp
        | succ j => exact hsp j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          have hbad : i.val + 1 ≤ 0 := hij
          omega
        | succ j => exact hsort i j (Fin.succ_le_succ_iff.mp hij)
    · intro i; cases i using Fin.cases with
      | zero => exact hpg
      | succ i => exact (hsp i).trans hpg

theorem full_projection_partition (hRR : RealRankZero D) {f g : D}
    (hf : IsStarProjection f) (hg : IsStarProjection g) (hfull : IsFull g) :
    ∃ n : ℕ, ∃ e : Fin n → D, (∀ i, IsStarProjection (e i)) ∧ (∑ i, e i = f) ∧
      ∀ i, ProjectionSubequivalent (e i) g := by
  obtain ⟨l, hl⟩ := exists_positive_fullness_frame hg.nonneg hfull
  let a : Fin l.length → D := l.get
  have ha : ∑ i, star (a i) * g * a i = 1 := by
    rw [← List.sum_ofFn]
    have hlist : List.ofFn (fun i => star (a i) * g * a i) =
        l.map (fun x => star x * g * x) := by
      change List.ofFn ((fun x : D => star x * g * x) ∘ l.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [hlist, hl]
  let v : Fin l.length → D := fun i => g * a i * f
  have hleft (i : Fin l.length) : g * v i = v i := by
    dsimp [v]; simp only [← mul_assoc, hg.isIdempotentElem.eq]
  have hvs (i : Fin l.length) : star (v i) * v i = f * (star (a i) * g * a i) * f := by
    dsimp [v]
    simp only [star_mul, hg.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc g g, hg.isIdempotentElem.eq]
  have hsum : ∑ i, star (v i) * v i = f := by
    simp_rw [hvs]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ha, mul_one, hf.isIdempotentElem]
  obtain ⟨e, he, _, hesum, hecomp⟩ := split_column hRR l.length hf (fun _ => g) v
    (fun _ => hg) hleft hsum
  exact ⟨l.length, e, he, hesum, hecomp⟩

end ProjectionSorting

section RoundingNumerics

lemma roundCoeff_zero_or_one {s : ℝ} (hs : s ∈ Set.Icc 0 1) (i : ℕ) :
    roundCoeff s i = 0 ∨ roundCoeff s i = 1 := by
  have hlow : ⌊s * (i : ℝ)⌋ ≤ ⌊s * (i + 1 : ℕ)⌋ :=
    Int.floor_mono (by push_cast; nlinarith [hs.1])
  have hupp : ⌊s * (i + 1 : ℕ)⌋ ≤ ⌊s * (i : ℝ)⌋ + 1 := by
    calc
      _ ≤ ⌊s * (i : ℝ) + 1⌋ := Int.floor_mono (by push_cast; nlinarith [hs.2])
      _ = _ := Int.floor_add_one _
  have h : (⌊s * (i + 1 : ℕ)⌋ - ⌊s * (i : ℝ)⌋ : ℤ) = 0 ∨
      (⌊s * (i + 1 : ℕ)⌋ - ⌊s * (i : ℝ)⌋ : ℤ) = 1 := by omega
  rcases h with h | h
  · left; simp only [roundCoeff, h, Int.cast_zero]
  · right; simp only [roundCoeff, h, Int.cast_one]

lemma roundDeficit_bounds (s : ℝ) (i : ℕ) :
    -1 ≤ roundDeficit s i ∧ roundDeficit s i ≤ 0 := by
  have h₁ := Int.floor_le (s * (i : ℝ))
  have h₂ := Int.lt_floor_add_one (s * (i : ℝ))
  dsimp [roundDeficit]
  constructor <;> linarith

lemma roundCoeff_sub (s : ℝ) (i : ℕ) :
    roundCoeff s i - s = roundDeficit s (i + 1) - roundDeficit s i := by
  dsimp only [roundCoeff, roundDeficit]
  push_cast
  ring

lemma weighted_differences_bounds (n : ℕ) (a t : ℕ → ℝ)
    (ha : ∀ i, -1 ≤ a i ∧ a i ≤ 0) (ht : ∀ i, 0 ≤ t i) (hmono : Antitone t) :
    -t 0 ≤ (∑ i ∈ Finset.range n, (a (i + 1) - a i) * t i) + a 0 * t 0 ∧
      (∑ i ∈ Finset.range n, (a (i + 1) - a i) * t i) + a 0 * t 0 ≤ 0 := by
  induction n generalizing a t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    constructor
    · simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right (ha 0).1 (ht 0)
    · exact mul_nonpos_of_nonpos_of_nonneg (ha 0).2 (ht 0)
  | succ n ih =>
    have hshift := ih (fun i => a (i + 1)) (fun i => t (i + 1))
      (fun i => ha (i + 1)) (fun i => ht (i + 1))
      (fun i j hij => hmono (Nat.add_le_add_right hij 1))
    have hδ : 0 ≤ t 0 - t 1 := sub_nonneg.mpr (hmono (Nat.zero_le 1))
    have hprodLow : -(t 0 - t 1) ≤ a 1 * (t 0 - t 1) := by
      simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right (ha 1).1 hδ
    have hprodUpp : a 1 * (t 0 - t 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (ha 1).2 hδ
    rw [Finset.sum_range_succ']
    have heq :
        (∑ i ∈ Finset.range n, (a (i + 1 + 1) - a (i + 1)) * t (i + 1)) +
          (a 1 - a 0) * t 0 + a 0 * t 0 =
        ((∑ i ∈ Finset.range n, (a (i + 1 + 1) - a (i + 1)) * t (i + 1)) +
          a 1 * t 1) + a 1 * (t 0 - t 1) := by ring
    simp only [zero_add] at *
    rw [heq]
    constructor <;> linarith

lemma floor_weighted_rounding {s M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hmono : Antitone t) (hbound : ∀ i, t i ≤ M) :
    |(∑ i : Fin n, roundCoeff s i * t i) - s * ∑ i, t i| ≤ M := by
  let T : ℕ → ℝ := fun i => if hi : i < n then t ⟨i, hi⟩ else 0
  have hT (i : ℕ) : 0 ≤ T i := by
    dsimp only [T]
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact le_rfl
  have hTM : T 0 ≤ M := by
    dsimp only [T]
    split_ifs with hi
    · exact hbound ⟨0, hi⟩
    · exact hM
  have hTmono : Antitone T := by
    intro i j hij
    by_cases hi : i < n
    · by_cases hj : j < n
      · simp only [T, dite_eq_left hi, dite_eq_left hj]
        exact hmono (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
      · simp only [T, dite_eq_left hi, dite_eq_right hj]
        exact ht ⟨i, hi⟩
    · have hj : ¬j < n := fun h => hi (lt_of_le_of_lt hij h)
      simp only [T, dite_eq_right hi, dite_eq_right hj, le_refl]
  have h := weighted_differences_bounds n (roundDeficit s) T (roundDeficit_bounds s) hT hTmono
  simp only [roundDeficit_zero, zero_mul, add_zero, ← roundCoeff_sub] at h
  have heq : (∑ i : Fin n, roundCoeff s i * t i) - s * ∑ i, t i =
      ∑ i ∈ Finset.range n, (roundCoeff s i - s) * T i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [T, dite_eq_left i.isLt]
  rw [heq, abs_le]
  exact ⟨by linarith [h.1], h.2.trans hM⟩

end RoundingNumerics

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

lemma trace_projection_real (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    τ.functional p = ((τ.functional p).re : ℂ) :=
  Complex.eq_re_of_ofReal_le (τ.functional.map_nonneg hp.nonneg)

lemma trace_projection_le_one (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    (τ.functional p).re ≤ 1 := by
  have h := (Complex.le_def.mp (τ.functional.monotone hp.le_one)).1
  change (τ.functional p).re ≤ (τ.functional 1).re at h
  simpa only [τ.normalized, Complex.one_re] using h

theorem proportional_projection_bound (hRR : RealRankZero D) {f g : D}
    (hf : IsStarProjection f) (hg : IsStarProjection g) (hfull : IsFull g)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧ ∀ τ : TracialState D,
      ‖τ.functional e - (s : ℂ) * τ.functional f‖ ≤ (τ.functional g).re := by
  classical
  obtain ⟨n, v, hv, hvsum, hvg⟩ := full_projection_partition hRR hf hg hfull
  obtain ⟨p, hp, hpsum, hsort, hpg⟩ :=
    comparison_sorted_partition hRR n hf hg v hv hvsum hvg
  let S : Finset (Fin n) := Finset.univ.filter (fun i => roundCoeff s i = 1)
  let e := ∑ i ∈ S, p i
  have hortho := projection_family_orthogonal hf p hp hpsum
  have he : IsStarProjection e := orthogonal_projection_sum S p (fun i _ => hp i)
    (fun _ _ _ _ hij => hortho hij)
  have hef : e ≤ f := by
    rw [← hpsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => (hp i).nonneg)
  refine ⟨e, he, hef, ?_⟩
  intro τ
  have htrace : (τ.functional e).re =
      ∑ i : Fin n, roundCoeff s i * (τ.functional (p i)).re := by
    simp only [e, map_sum, Complex.re_sum, S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases roundCoeff_zero_or_one hs i with h | h <;> simp only [h] <;> norm_num
  have hsum : (τ.functional f).re = ∑ i, (τ.functional (p i)).re := by
    rw [← hpsum, map_sum, Complex.re_sum]
  have hb := floor_weighted_rounding (s := s) (τ.functional.map_nonneg hg.nonneg).1 n
    (fun i => (τ.functional (p i)).re)
    (fun i => (τ.functional.map_nonneg (hp i).nonneg).1)
    (fun i j hij => ProjectionSubequivalent.trace_le τ (hp j) (hp i) (hsort i j hij))
    (fun i => ProjectionSubequivalent.trace_le τ (hp i) hg (hpg i))
  rw [trace_projection_real τ he, trace_projection_real τ hf,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    htrace, hsum]
  exact hb

lemma proportional_subprojection (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {f : D} (hf : IsStarProjection f) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧ ∀ τ : TracialState D,
      ‖τ.functional e - (s : ℂ) * τ.functional f‖ < ε := by
  obtain ⟨g, hg, hgfull, hgsmall⟩ := hsmall ε hε
  obtain ⟨e, he, hef, hbound⟩ := proportional_projection_bound hRR hf hg hgfull hs
  refine ⟨e, he, hef, fun τ => lt_of_le_of_lt (hbound τ) ?_⟩
  have hbg : BddAbove (Set.range (fun τ : TracialState D => (τ.functional g).re)) :=
    ⟨1, by rintro _ ⟨τ, rfl⟩; exact trace_projection_le_one τ hg⟩
  exact (le_ciSup hbg τ).trans_lt hgsmall

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

lemma trace_compression_error (τ : TracialState D) {e q : D}
    (he : IsStarProjection e) (hq : IsStarProjection q) (heq : e ≤ q)
    (b : D) (α : ℂ) :
    ‖τ.functional (e * b) - α * τ.functional e‖ ≤
      ‖q * b * q - α • q‖ * (τ.functional e).re := by
  have heq' := (he.le_iff_mul_eq_left hq).mp heq
  have hqe' := (he.le_iff_mul_eq_right hq).mp heq
  have htrace : τ.functional (e * (q * b * q - α • q)) =
      τ.functional (e * b) - α * τ.functional e := by
    rw [mul_sub, mul_smul_comm, heq', map_sub, map_smul]
    change τ.functional (e * (q * b * q)) - α * τ.functional e = _
    congr 1
    calc
      _ = τ.functional (e * b * q) := by rw [← mul_assoc, ← mul_assoc, heq']
      _ = τ.functional (q * (e * b)) := τ.tracial _ _
      _ = _ := by rw [← mul_assoc, hqe']
  rw [← htrace]
  exact trace_norm_projection_mul_le τ he _

lemma scalar_splitting_error (τ : TracialState D) {e q : D}
    (he : IsStarProjection e) (hq : IsStarProjection q) (heq : e ≤ q)
    {s γ : ℝ} (hs : 0 ≤ s) (b : D) (α : ℂ)
    (hγ : ‖q * b * q - α • q‖ ≤ γ) :
    ‖τ.functional (e * b) - (s : ℂ) * τ.functional (q * b)‖ ≤
      γ * ((τ.functional e).re + s * (τ.functional q).re) +
      ‖α‖ * ‖τ.functional e - (s : ℂ) * τ.functional q‖ := by
  have hbe := (trace_compression_error τ he hq heq b α).trans
    (mul_le_mul_of_nonneg_right hγ (τ.functional.map_nonneg he.nonneg).1)
  have hbq := (trace_compression_error τ hq hq le_rfl b α).trans
    (mul_le_mul_of_nonneg_right hγ (τ.functional.map_nonneg hq.nonneg).1)
  have heqv : τ.functional (e * b) - (s : ℂ) * τ.functional (q * b) =
      (τ.functional (e * b) - α * τ.functional e) +
      α * (τ.functional e - (s : ℂ) * τ.functional q) +
      (s : ℂ) * (α * τ.functional q - τ.functional (q * b)) := by ring
  rw [heqv]
  calc
    _ ≤ ‖τ.functional (e * b) - α * τ.functional e‖ +
        ‖α * (τ.functional e - (s : ℂ) * τ.functional q)‖ +
        ‖(s : ℂ) * (α * τ.functional q - τ.functional (q * b))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ = ‖τ.functional (e * b) - α * τ.functional e‖ +
        ‖α‖ * ‖τ.functional e - (s : ℂ) * τ.functional q‖ +
        s * ‖τ.functional (q * b) - α * τ.functional q‖ := by
      rw [norm_mul, norm_mul, norm_sub_rev (α * _), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ γ * (τ.functional e).re +
        ‖α‖ * ‖τ.functional e - (s : ℂ) * τ.functional q‖ +
        s * (γ * (τ.functional q).re) := by gcongr
    _ = _ := by ring

theorem split_finite_linear_tests (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {q : D} (hq : IsStarProjection q) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (F : Finset D) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ b ∈ F, ∀ τ : TracialState D,
      ‖τ.functional (e * b) - (s : ℂ) * τ.functional (q * b)‖ < ε := by
  classical
  let γ := ε / 4
  have hγ : 0 < γ := div_pos hε (by norm_num)
  obtain ⟨P, hP⟩ := scalar_compressions hRR hq F hγ
  choose α hα using (fun i : P.Index => fun b : F => hP b.val b.property i)
  let M := ∑ i : P.Index, ∑ b : F, ‖α i b‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  let δ := ε / (4 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hpieces := fun i : P.Index => proportional_subprojection hRR hsmall
    (P.isProjection i) hs hδ
  choose E hE hEP hEtrace using hpieces
  have horth : Pairwise (fun i j => E i * E j = 0) := by
    intro i j hij
    exact mul_eq_zero_of_supports ((hE i).le_iff_mul_eq_left (P.isProjection i) |>.mp (hEP i))
      ((hE j).le_iff_mul_eq_right (P.isProjection j) |>.mp (hEP j)) (P.orthogonal hij)
  let e := ∑ i : P.Index, E i
  have he : IsStarProjection e := orthogonal_projection_sum Finset.univ E
    (fun i _ => hE i) (fun _ _ _ _ hij => horth hij)
  have heq : e ≤ q := by
    rw [← P.sum_eq]
    exact Finset.sum_le_sum fun i _ => hEP i
  refine ⟨e, he, heq, ?_⟩
  intro b hb τ
  let B : F := ⟨b, hb⟩
  have hscalars : (∑ i : P.Index, ‖α i B‖) ≤ M := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun x _ => norm_nonneg _) (Finset.mem_univ B)
  have hte : (∑ i : P.Index, (τ.functional (E i)).re) = (τ.functional e).re := by
    simp only [e, map_sum, Complex.re_sum]
  have htq : (∑ i : P.Index, (τ.functional (P.piece i)).re) = (τ.functional q).re := by
    have h := congrArg (fun x => (τ.functional x).re) P.sum_eq
    simpa only [map_sum, Complex.re_sum] using h
  have hmass : (τ.functional e).re + s * (τ.functional q).re ≤ 2 := by
    have hq0 := (τ.functional.map_nonneg hq.nonneg).1
    have hq1 := trace_projection_le_one τ hq
    have he1 := trace_projection_le_one τ he
    nlinarith [hs.1, hs.2]
  have hδM : δ * M ≤ ε / 4 := by
    have heqδ : δ * (4 * (M + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt (by positivity))
    nlinarith [hδ.le]
  have hsum : τ.functional (e * b) - (s : ℂ) * τ.functional (q * b) =
      ∑ i : P.Index, (τ.functional (E i * b) - (s : ℂ) * τ.functional (P.piece i * b)) := by
    calc
      _ = τ.functional ((∑ i, E i) * b) -
          (s : ℂ) * τ.functional ((∑ i, P.piece i) * b) := by rw [P.sum_eq]
      _ = _ := by simp only [Finset.sum_mul, map_sum,
        Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  calc
    _ ≤ ∑ i : P.Index, ‖τ.functional (E i * b) -
        (s : ℂ) * τ.functional (P.piece i * b)‖ := norm_sum_le _ _
    _ ≤ ∑ i : P.Index, (γ * ((τ.functional (E i)).re + s * (τ.functional (P.piece i)).re)
        + ‖α i B‖ * δ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (scalar_splitting_error τ (hE i) (P.isProjection i) (hEP i)
        hs.1 b (α i B) (hα i B).le).trans
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hEtrace i τ).le (norm_nonneg _)))
    _ = γ * ((τ.functional e).re + s * (τ.functional q).re) +
        δ * ∑ i : P.Index, ‖α i B‖ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, hte, htq, ← Finset.sum_mul, mul_comm _ δ]
    _ ≤ γ * 2 + δ * M := add_le_add
      (mul_le_mul_of_nonneg_left hmass hγ.le) (mul_le_mul_of_nonneg_left hscalars hδ.le)
    _ ≤ γ * 2 + ε / 4 := add_le_add (le_refl _) hδM
    _ < ε := by dsimp [γ]; linarith

end FiniteLinearTests

section OrthogonalInsertion

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_mul_mono_right (τ : TracialState D) {a b c : D} (ha : 0 ≤ a) (hbc : b ≤ c) :
    (τ.functional (a * b)).re ≤ (τ.functional (a * c)).re := by
  have h := (trace_mul_nonneg τ ha (sub_nonneg.mpr hbc)).1
  simp only [mul_sub, map_sub, Complex.sub_re, Complex.zero_re] at h
  linarith

lemma trace_mul_mono_left (τ : TracialState D) {a b c : D} (hc : 0 ≤ c) (hab : a ≤ b) :
    (τ.functional (a * c)).re ≤ (τ.functional (b * c)).re := by
  rw [τ.tracial a c, τ.tracial b c]
  exact trace_mul_mono_right τ hc hab

lemma trace_projection_difference_sq (τ : TracialState D) {t y : D}
    (ht : IsStarProjection t) (hy : IsStarProjection y) :
    traceTwoNorm τ (t - y) ^ 2 =
      (τ.functional t).re + (τ.functional y).re - 2 * (τ.functional (t * y)).re := by
  rw [traceTwoNorm_sq]
  simp only [star_sub, ht.isSelfAdjoint.star_eq, hy.isSelfAdjoint.star_eq,
    sub_mul, mul_sub, ht.isIdempotentElem.eq, hy.isIdempotentElem.eq, map_sub,
    Complex.sub_re, τ.tracial y t]
  ring

lemma projection_difference_linear (τ : TracialState D) {t y : D}
    (ht : IsStarProjection t) (hy : IsStarProjection y)
    (hmass : (τ.functional t).re ≤ (τ.functional y).re) {x : D} (hx : ‖x‖ ≤ 1) :
    ‖τ.functional ((t - y) * x)‖ ≤
      2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y) := by
  have hts : traceTwoNorm τ t ≤ traceTwoNorm τ y := by
    have h := Real.sqrt_le_sqrt hmass
    simpa only [traceTwoNorm, ht.isSelfAdjoint.star_eq, ht.isIdempotentElem.eq,
      hy.isSelfAdjoint.star_eq, hy.isIdempotentElem.eq] using h
  have hxy : traceTwoNorm τ ((t - y) * x) ≤ traceTwoNorm τ (t - y) :=
    (traceTwoNorm_mul_right τ x (t - y)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (traceTwoNorm_nonneg τ _))
  have hyx : traceTwoNorm τ (y * x) ≤ traceTwoNorm τ y :=
    (traceTwoNorm_mul_right τ x y).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (traceTwoNorm_nonneg τ _))
  have hdecomp : (t - y) * x = t * ((t - y) * x) + (t - y) * (y * x) := by
    calc
      _ = (t * (t - y) + (t - y) * y) * x := by
        simp only [mul_sub, sub_mul, ht.isIdempotentElem.eq, hy.isIdempotentElem.eq]
        noncomm_ring
      _ = _ := by noncomm_ring
  rw [hdecomp, map_add]
  calc
    _ ≤ ‖τ.functional (t * ((t - y) * x))‖ + ‖τ.functional ((t - y) * (y * x))‖ :=
      norm_add_le _ _
    _ ≤ traceTwoNorm τ t * traceTwoNorm τ ((t - y) * x) +
        traceTwoNorm τ (t - y) * traceTwoNorm τ (y * x) :=
      add_le_add (trace_norm_mul_le τ _ _) (trace_norm_mul_le τ _ _)
    _ ≤ traceTwoNorm τ y * traceTwoNorm τ (t - y) +
        traceTwoNorm τ (t - y) * traceTwoNorm τ y :=
      add_le_add
        (mul_le_mul hts hxy (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _))
        (mul_le_mul_of_nonneg_left hyx (traceTwoNorm_nonneg τ _))
    _ = _ := by
      have hyv : traceTwoNorm τ y = Real.sqrt (τ.functional y).re := by
        simp only [traceTwoNorm, hy.isSelfAdjoint.star_eq, hy.isIdempotentElem.eq]
      rw [hyv]; ring

lemma projection_insert_normalized {f h : D} (hf : IsStarProjection f)
    (hh : IsStarProjection h) {c : ℝ} (hc : 0 < c) (hbound : c • f ≤ f * h * f) :
    ∃ t : D, IsStarProjection t ∧ t ≤ h ∧ f * t * f = f * h * f ∧
      ∀ τ : TracialState D, τ.functional t = τ.functional f := by
  obtain ⟨z, hz, hn⟩ := exists_corner_normalizer hf hh.nonneg hc hbound
  let a := f * h * f
  have hzf : (z : D) * f = z := z.property.2
  have hfz : f * (z : D) = z := z.property.1
  have haf : a * f = a := by dsimp [a]; rw [mul_assoc, hf.isIdempotentElem]
  have hfa : f * a = a := by dsimp [a]; rw [← mul_assoc, ← mul_assoc, hf.isIdempotentElem]
  have hzan : (z : D) * a * (z : D) = f := by
    calc
      _ = ((z : D) * f) * h * (f * (z : D)) := by dsimp [a]; simp only [mul_assoc]
      _ = (z : D) * h * (z : D) := by rw [hzf, hfz]
      _ = f := hn
  have haz : a * (z : D) = (z : D) * a := by
    calc
      _ = f * (a * (z : D)) := by rw [← mul_assoc, hfa]
      _ = ((z : D) * a * (z : D)) * (a * (z : D)) := by rw [hzan]
      _ = (z : D) * a * ((z : D) * a * (z : D)) := by simp only [mul_assoc]
      _ = (z : D) * a := by rw [hzan, mul_assoc, haf]
  let v := h * (z : D)
  have hv : star v * v = f := by
    dsimp [v]
    rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe hf hz).star_eq,
      hh.isSelfAdjoint.star_eq]
    simpa only [mul_assoc, ← mul_assoc h h, hh.isIdempotentElem.eq] using hn
  have hhv : h * v = v := by dsimp [v]; rw [← mul_assoc, hh.isIdempotentElem]
  have ht : IsStarProjection (v * star v) :=
    ⟨isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star.mp
      (hv ▸ hf.isIdempotentElem), by simp only [IsSelfAdjoint, star_mul, star_star]⟩
  have hth : v * star v ≤ h := (ht.le_iff_mul_eq_right hh).mpr (by rw [← mul_assoc, hhv])
  refine ⟨v * star v, ht, hth, ?_, fun τ => ?_⟩
  · have hfv : f * v = a * (z : D) := by
      dsimp [v, a]; simp only [mul_assoc, hfz]
    have hvf : star v * f = (z : D) * a := by
      dsimp [v, a]
      rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe hf hz).star_eq, hh.isSelfAdjoint.star_eq]
      simp only [← mul_assoc, hzf]
    calc
      _ = (f * v) * (star v * f) := by simp only [mul_assoc]
      _ = (a * (z : D)) * ((z : D) * a) := by rw [hfv, hvf]
      _ = ((z : D) * a * (z : D)) * a := by rw [haz]; simp only [mul_assoc]
      _ = a := by rw [hzan, hfa]
      _ = _ := rfl
  · rw [τ.tracial v (star v), hv]

theorem orthogonal_insertion (hRR : RealRankZero D) {z y : D}
    (hz : IsStarProjection z) (hy : IsStarProjection y) :
    ∃ t : D, IsStarProjection t ∧ t ≤ 1 - z ∧ ∀ τ : TracialState D,
      ((τ.functional y).re - 3 * (τ.functional (y * z)).re ≤ (τ.functional t).re ∧
      (τ.functional t).re ≤ (τ.functional y).re) ∧
      traceTwoNorm τ (t - y) ^ 2 ≤ 5 * (τ.functional (y * z)).re ∧
      ∀ x : D, ‖x‖ ≤ 1 → ‖τ.functional ((t - y) * x)‖ ≤
        2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y) := by
  obtain ⟨d, hd, hdy, hlow, hupp⟩ := exists_column_cut hRR hy hz.isSelfAdjoint
  let f := y - d
  have hf : IsStarProjection f := (hd.le_iff_sub hy).mp hdy
  have hfy : f ≤ y := by dsimp [f]; exact sub_le_self _ hd.nonneg
  have hfd : f + d = y := by dsimp [f]; abel
  have hbound : (3 / 8 : ℝ) • f ≤ f * (1 - z) * f := by
    have heq : f * (1 - z) * f = f - f * z * f := by
      rw [mul_sub f 1 z, mul_one, sub_mul, hf.isIdempotentElem]
    rw [heq]
    change f * z * f ≤ (5 / 8 : ℝ) • f at hupp
    have heqf : f - (5 / 8 : ℝ) • f = (3 / 8 : ℝ) • f := by module
    have h := sub_le_sub (le_refl f) hupp
    rwa [heqf] at h
  obtain ⟨t, ht, htz, hftf, htrace⟩ := projection_insert_normalized hf hz.one_sub
    (by norm_num : (0 : ℝ) < 3 / 8) hbound
  refine ⟨t, ht, htz, ?_⟩
  intro τ
  have htf : (τ.functional t).re = (τ.functional f).re := congrArg Complex.re (htrace τ)
  have htd : (τ.functional f).re + (τ.functional d).re = (τ.functional y).re := by
    have h := congrArg (fun x => (τ.functional x).re) hfd
    simpa only [map_add, Complex.add_re] using h
  have hyz0 : 0 ≤ (τ.functional (y * z)).re := (trace_mul_nonneg τ hy.nonneg hz.nonneg).1
  have hdz : (τ.functional (d * z)).re ≤ (τ.functional (y * z)).re :=
    trace_mul_mono_left τ hz.nonneg hdy
  have hsz : (3 / 8 : ℝ) * (τ.functional d).re ≤ (τ.functional (d * z)).re := by
    have h := (Complex.le_def.mp (τ.functional.monotone hlow)).1
    change (τ.functional ((3 / 8 : ℝ) • d)).re ≤ (τ.functional (d * z * d)).re at h
    rw [τ.functional.map_smul_of_tower, trace_projection_corner τ hd, Complex.smul_re, smul_eq_mul] at h
    exact h
  have hmasslow : (τ.functional y).re - 3 * (τ.functional (y * z)).re ≤ (τ.functional t).re := by
    linarith
  have hmassup : (τ.functional t).re ≤ (τ.functional y).re := by
    rw [htf]
    exact (Complex.le_def.mp (τ.functional.monotone hfy)).1
  have hty : (τ.functional f).re - (τ.functional (f * z)).re ≤
      (τ.functional (t * y)).re := by
    have heqt : τ.functional (t * f) = τ.functional f - τ.functional (f * z) := by
      rw [τ.tracial t f, ← trace_projection_corner τ hf t, hftf,
        trace_projection_corner τ hf (1 - z), mul_sub, mul_one, map_sub]
    rw [← Complex.sub_re, ← heqt]
    exact trace_mul_mono_right τ ht.nonneg hfy
  have hfz : (τ.functional (f * z)).re ≤ (τ.functional (y * z)).re :=
    trace_mul_mono_left τ hz.nonneg hfy
  refine ⟨⟨hmasslow, hmassup⟩, ?_, fun x hx => projection_difference_linear τ ht hy hmassup hx⟩
  rw [trace_projection_difference_sq τ ht hy]
  linarith

end OrthogonalInsertion

section MatrixRows

variable {D : Type uD} [CStarAlgebra D]

namespace ProjectionRow

variable {I : Type uI} [Fintype I] {q : D} (U : ProjectionRow I q)

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

lemma sample_star (a : D) : star (U.sample a) = U.sample (star a) := by
  simp only [sample, star_sum, U.coeff_star]

lemma sample_mul (a b : D) (hb : q * b = b) :
    U.sample a * U.sample b = U.sample (a * b) := by
  classical
  simp only [sample, Finset.sum_mul, Finset.mul_sum, U.coeff_mul a b hb]
  simp

lemma sample_projection {e : D} (he : IsStarProjection e) (hqe : q * e = e) :
    IsStarProjection (U.sample e) := by
  constructor
  · change U.sample e * U.sample e = U.sample e
    rw [U.sample_mul _ _ hqe, he.isIdempotentElem.eq]
  · change star (U.sample e) = U.sample e
    rw [U.sample_star, he.isSelfAdjoint.star_eq]

lemma range_projection : IsStarProjection (U.sample q) :=
  U.sample_projection U.projection U.projection.isIdempotentElem

lemma sample_le [PartialOrder D] [StarOrderedRing D] {e : D}
    (he : IsStarProjection e) (heq : e ≤ q) : U.sample e ≤ U.sample q := by
  have hqe := (he.le_iff_mul_eq_right U.projection).mp heq
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  apply ((U.sample_projection he hqe).le_iff_mul_eq_left U.range_projection).mpr
  rw [U.sample_mul _ _ U.projection.isIdempotentElem, heq']

lemma matrix_star (a : D) (s : Matrix I I ℂ) :
    star (U.matrix a s) = U.matrix (star a) (star s) := by
  simp only [matrix, star_sum, star_smul, U.coeff_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

lemma matrix_mul (a b : D) (hb : q * b = b) (s t : Matrix I I ℂ) :
    U.matrix a s * U.matrix b t = U.matrix (a * b) (s * t) := by
  classical
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (s i j * t k l) •
        (if j = k then U.coeff (a * b) i l else 0) := by
      unfold matrix
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      rw [smul_mul_smul_comm, U.coeff_mul a b hb]
    _ = ∑ i, ∑ j, ∑ l, (s i j * t j l) • U.coeff (a * b) i l := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
      simp
    _ = U.matrix (a * b) (s * t) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Finset.sum_smul]

lemma matrix_one [DecidableEq I] (a : D) : U.matrix a 1 = U.sample a := by
  classical
  simp [matrix, sample, Matrix.one_apply]

lemma sample_matrix (a b : D) (hb : q * b = b) (s : Matrix I I ℂ) :
    U.sample a * U.matrix b s = U.matrix (a * b) s := by
  classical
  rw [← U.matrix_one, U.matrix_mul _ _ hb, one_mul]

lemma matrix_sample (a b : D) (hb : q * b = b) (s : Matrix I I ℂ) :
    U.matrix a s * U.sample b = U.matrix (a * b) s := by
  classical
  rw [← U.matrix_one, U.matrix_mul _ _ hb, mul_one]

lemma trace_coeff [DecidableEq I] [PartialOrder D] (τ : TracialState D) (a : D) (ha : a * q = a)
    (i j : I) : τ.functional (U.coeff a i j) = if i = j then τ.functional a else 0 := by
  classical
  rw [coeff, τ.tracial (U.entry i * a) (star (U.entry j)), ← mul_assoc]
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, U.gram_diag, τ.tracial q a, ha]
  · rw [ite_eq_right h, U.gram_offdiag j i (Ne.symm h), zero_mul, map_zero]

lemma trace_sample [PartialOrder D] (τ : TracialState D) (a : D) (ha : a * q = a) :
    τ.functional (U.sample a) = (Fintype.card I : ℂ) * τ.functional a := by
  classical
  simp only [sample, map_sum, U.trace_coeff τ a ha, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma trace_matrix [PartialOrder D] (τ : TracialState D) (a : D) (ha : a * q = a)
    (s : Matrix I I ℂ) : τ.functional (U.matrix a s) = Matrix.trace s * τ.functional a := by
  classical
  simp [matrix, U.trace_coeff τ a ha, Matrix.trace, Finset.sum_mul]

lemma matrix_sample_commute {e : D}
    (hqe : q * e = e) (heq : e * q = e) (s : Matrix I I ℂ) :
    Commute (U.matrix q s) (U.sample e) := by
  rw [commute_iff_eq, U.matrix_sample _ _ hqe, U.sample_matrix _ _ U.projection.isIdempotentElem,
    hqe, heq]

end ProjectionRow

end MatrixRows

section SamplingEstimates

lemma proportional_complex_bound {u v : ℂ} {a b C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : ‖u‖ ≤ C * a) (hv : ‖v‖ ≤ C * b)
    (hcross : u * (b : ℂ) = v * (a : ℂ)) (c : ℝ) :
    ‖u - (c : ℂ) * v‖ ≤ C * |a - c * b| := by
  by_cases hb : b = 0
  · have ha0 : a = 0 := le_antisymm (hb ▸ hab) ha
    have hu0 : u = 0 := norm_le_zero_iff.mp (by simpa only [ha0, mul_zero] using hu)
    have hv0 : v = 0 := norm_le_zero_iff.mp (by simpa only [hb, mul_zero] using hv)
    simp [ha0, hb, hu0, hv0]
  · have hbpos : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
    let α : ℂ := v / (b : ℂ)
    have hvEq : v = α * (b : ℂ) := by dsimp [α]; rw [div_mul_cancel₀ _ hbC]
    have huEq : u = α * (a : ℂ) := by
      calc
        _ = (v * (a : ℂ)) / (b : ℂ) := (eq_div_iff hbC).mpr hcross
        _ = _ := by dsimp [α]; ring
    have hα : ‖α‖ ≤ C := by
      dsimp [α]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
      exact (div_le_iff₀ hbpos).mpr hv
    have hdiff : u - (c : ℂ) * v = α * ((a - c * b : ℝ) : ℂ) := by
      rw [huEq, hvEq]
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hα (abs_nonneg _)

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma norm_square_difference (a b : D) :
    ‖star a * a - star b * b‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  calc
    _ = ‖star a * (a - b) + star (a - b) * b‖ := by
      congr 1; rw [star_sub]; noncomm_ring
    _ ≤ ‖star a * (a - b)‖ + ‖star (a - b) * b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖a - b‖ + ‖a - b‖ * ‖b‖ := by
      simpa only [norm_star] using add_le_add (norm_mul_le (star a) (a - b))
        (norm_mul_le (star (a - b)) b)
    _ = _ := by ring

lemma trace_supported_norm_le (τ : TracialState D) {p a : D}
    (hp : IsStarProjection p) (hpa : p * a = a) :
    ‖τ.functional a‖ ≤ ‖a‖ * (τ.functional p).re := by
  simpa only [hpa] using trace_norm_projection_mul_le τ hp a

lemma sampling_compression_estimates (τ : TracialState D) {p y z x : D}
    (hp : IsStarProjection p) (hy : IsStarProjection y) (hyp : y ≤ p)
    (hyz : Commute y z) (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 2)
    {η : ℝ} (hclose : ‖p * x * p - z‖ ≤ η) :
    ‖τ.functional (y * x) - τ.functional (z * y)‖ ≤ η * (τ.functional y).re ∧
    |traceTwoNorm τ (y * x * y) ^ 2 - (τ.functional (star z * z * y)).re| ≤
      3 * η * (τ.functional y).re := by
  have hyp' := (hy.le_iff_mul_eq_left hp).mp hyp
  have hpy := (hy.le_iff_mul_eq_right hp).mp hyp
  have hyz' : y * z = z * y := hyz.eq
  have hym0 : 0 ≤ (τ.functional y).re := (τ.functional.map_nonneg hy.nonneg).1
  constructor
  · have ht : τ.functional (y * (p * x * p - z)) =
        τ.functional (y * x) - τ.functional (z * y) := by
      rw [mul_sub, map_sub, τ.tracial y z]
      congr 1
      calc
        _ = τ.functional (y * x * p) := by rw [← mul_assoc, ← mul_assoc, hyp']
        _ = τ.functional (p * (y * x)) := τ.tracial _ _
        _ = _ := by rw [← mul_assoc, hpy]
    rw [← ht]
    exact (trace_norm_projection_mul_le τ hy _).trans
      (mul_le_mul_of_nonneg_right hclose hym0)
  · let R := y * x * y
    let S := z * y
    have hdf : R - S = y * (p * x * p - z) * y := by
      have hpx : y * (p * x * p) * y = y * x * y := by
        calc
          _ = (y * p) * x * (p * y) := by noncomm_ring
          _ = _ := by rw [hyp', hpy]
      have hzy : y * z * y = z * y := by
        rw [hyz', mul_assoc z y y, hy.isIdempotentElem]
      dsimp [R, S]
      rw [mul_sub, sub_mul, hpx, hzy]
    have hRS : ‖R - S‖ ≤ η := by
      rw [hdf]
      exact (norm_compress_le hy _).trans hclose
    have hR : ‖R‖ ≤ 1 := (norm_compress_le hy x).trans hx
    have hS : ‖S‖ ≤ 2 := by
      calc
        _ ≤ ‖z‖ * ‖y‖ := norm_mul_le _ _
        _ ≤ 2 * 1 := mul_le_mul hz (IsStarProjection.norm_le y hy) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hsq : ‖star R * R - star S * S‖ ≤ 3 * η := by
      exact (norm_square_difference R S).trans
        ((mul_le_mul (by linarith : ‖R‖ + ‖S‖ ≤ 3) hRS (norm_nonneg _)
         (by norm_num : (0 : ℝ) ≤ 3)))
    have hRy : R * y = R := by dsimp [R]; rw [mul_assoc, hy.isIdempotentElem]
    have hSy : S * y = S := by dsimp [S]; rw [mul_assoc, hy.isIdempotentElem]
    have hyR : y * star R = star R := by
      simpa only [star_mul, hy.isSelfAdjoint.star_eq] using congrArg star hRy
    have hyS : y * star S = star S := by
      simpa only [star_mul, hy.isSelfAdjoint.star_eq] using congrArg star hSy
    have hsup : y * (star R * R - star S * S) = star R * R - star S * S := by
      rw [mul_sub, ← mul_assoc y (star R), hyR, ← mul_assoc y (star S), hyS]
    have hnorm := (trace_supported_norm_le τ hy hsup).trans
      (mul_le_mul_of_nonneg_right hsq hym0)
    have htrS : τ.functional (star S * S) = τ.functional (star z * z * y) := by
      dsimp [S]
      rw [star_mul, hy.isSelfAdjoint.star_eq]
      calc
        _ = τ.functional (y * (star z * z) * y) := by simp only [mul_assoc]
        _ = τ.functional (y * (star z * z)) := trace_projection_corner τ hy _
        _ = _ := τ.tracial _ _
    have hreal := (Complex.abs_re_le_norm (τ.functional (star R * R - star S * S))).trans hnorm
    simpa only [map_sub, Complex.sub_re, htrS, traceTwoNorm_sq] using hreal

end SamplingEstimates

section SamplingConclusion

lemma complex_difference_transfer (a b u v : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ‖a - (c : ℂ) * b‖ ≤ ‖a - u‖ + ‖u - (c : ℂ) * v‖ + c * ‖b - v‖ := by
  calc
    _ = ‖(a - u) + (u - (c : ℂ) * v) + (c : ℂ) * (v - b)‖ := by congr 1; ring
    _ ≤ ‖a - u‖ + ‖u - (c : ℂ) * v‖ + ‖(c : ℂ) * (v - b)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, norm_sub_rev v b]

lemma real_difference_transfer (a b u v : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    |a - c * b| ≤ |a - u| + |u - c * v| + c * |b - v| := by
  calc
    _ = |(a - u) + (u - c * v) + c * (v - b)| := by congr 1; ring
    _ ≤ |a - u| + |u - c * v| + |c * (v - b)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = _ := by rw [abs_mul, abs_of_nonneg hc, abs_sub_comm v b]

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma sampling_via_scalar_reference (τ : TracialState D) {p y z : D}
    (hp : IsStarProjection p) (hy : IsStarProjection y) (hyp : y ≤ p)
    (hpz : Commute p z) (hyz : Commute y z) (x : unitary D)
    {η c : ℝ} (hη : η < 1) (hc : 0 ≤ c)
    (hclose : ‖p * (x : D) * p - z‖ < η)
    (hlin : τ.functional (z * y) * τ.functional p =
      τ.functional (z * p) * τ.functional y)
    (hsq : τ.functional (star z * z * y) * τ.functional p =
      τ.functional (star z * z * p) * τ.functional y) :
    ‖τ.functional (y * (x : D)) - (c : ℂ) * τ.functional (p * (x : D))‖ ≤
      η * ((τ.functional y).re + c * (τ.functional p).re) +
        2 * |(τ.functional y).re - c * (τ.functional p).re| ∧
    |traceTwoNorm τ ((x : D) * y - y * (x : D)) ^ 2 -
        c * traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2| ≤
      6 * η * ((τ.functional y).re + c * (τ.functional p).re) +
        10 * |(τ.functional y).re - c * (τ.functional p).re| := by
  have hx : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.norm_le (1 : D) (IsStarProjection.one D))
  have hz : ‖z‖ ≤ 2 := by
    have h1 := norm_le_norm_sub_add z (p * (x : D) * p)
    rw [norm_sub_rev z] at h1
    have h2 := (norm_compress_le hp (x : D)).trans hx
    linarith
  have hym : 0 ≤ (τ.functional y).re := (τ.functional.map_nonneg hy.nonneg).1
  have hpm : 0 ≤ (τ.functional p).re := (τ.functional.map_nonneg hp.nonneg).1
  have hymp : (τ.functional y).re ≤ (τ.functional p).re :=
    (Complex.le_def.mp (τ.functional.monotone hyp)).1
  have hnorm (r : D) (hr : IsStarProjection r) :
      ‖τ.functional (z * r)‖ ≤ 2 * (τ.functional r).re := by
    rw [τ.tracial z r]
    exact (trace_norm_projection_mul_le τ hr z).trans
      (mul_le_mul_of_nonneg_right hz (τ.functional.map_nonneg hr.nonneg).1)
  have hzsq : ‖star z * z‖ ≤ 4 := by
    have h := norm_mul_le (star z) z
    rw [norm_star] at h
    nlinarith [norm_nonneg z]
  have hnormsq (r : D) (hr : IsStarProjection r) :
      ‖τ.functional (star z * z * r)‖ ≤ 4 * (τ.functional r).re := by
    rw [τ.tracial (star z * z) r]
    exact (trace_norm_projection_mul_le τ hr _).trans
      (mul_le_mul_of_nonneg_right hzsq (τ.functional.map_nonneg hr.nonneg).1)
  rw [trace_projection_real τ hp, trace_projection_real τ hy] at hlin hsq
  have hlin' := proportional_complex_bound hym hymp (hnorm y hy) (hnorm p hp) hlin c
  have hsq' := proportional_complex_bound hym hymp (hnormsq y hy) (hnormsq p hp) hsq c
  have hsqreal : |(τ.functional (star z * z * y)).re -
      c * (τ.functional (star z * z * p)).re| ≤
        4 * |(τ.functional y).re - c * (τ.functional p).re| := by
    have h := (Complex.abs_re_le_norm (τ.functional (star z * z * y) -
      (c : ℂ) * τ.functional (star z * z * p))).trans hsq'
    simpa using h
  obtain ⟨ey, sy⟩ := sampling_compression_estimates τ hp hy hyp hyz hx hz hclose.le
  obtain ⟨ep, sp⟩ := sampling_compression_estimates τ hp hp le_rfl hpz hx hz hclose.le
  constructor
  · exact (complex_difference_transfer _ _ _ _ hc).trans
      ((add_le_add (add_le_add ey hlin') (mul_le_mul_of_nonneg_left ep hc)).trans_eq
        (by ring))
  · have henergy : |traceTwoNorm τ (y * (x : D) * y) ^ 2 -
        c * traceTwoNorm τ (p * (x : D) * p) ^ 2| ≤
        3 * η * ((τ.functional y).re + c * (τ.functional p).re) +
          4 * |(τ.functional y).re - c * (τ.functional p).re| := by
      exact (real_difference_transfer _ _ _ _ hc).trans
        ((add_le_add (add_le_add sy hsqreal) (mul_le_mul_of_nonneg_left sp hc)).trans_eq
          (by ring))
    rw [unitary_commutator_energy τ x hy, unitary_commutator_energy τ x hp]
    calc
      _ = |2 * ((τ.functional y).re - c * (τ.functional p).re) -
          2 * (traceTwoNorm τ (y * (x : D) * y) ^ 2 -
            c * traceTwoNorm τ (p * (x : D) * p) ^ 2)| := by congr 1; ring
      _ ≤ |2 * ((τ.functional y).re - c * (τ.functional p).re)| +
          |2 * (traceTwoNorm τ (y * (x : D) * y) ^ 2 -
            c * traceTwoNorm τ (p * (x : D) * p) ^ 2)| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (2 * ((τ.functional y).re - c * (τ.functional p).re)) 0 (2 * (traceTwoNorm τ (y * (x : D) * y) ^ 2 - c * traceTwoNorm τ (p * (x : D) * p) ^ 2))
      _ = 2 * |(τ.functional y).re - c * (τ.functional p).re| +
          2 * |traceTwoNorm τ (y * (x : D) * y) ^ 2 -
            c * traceTwoNorm τ (p * (x : D) * p) ^ 2| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * |(τ.functional y).re - c * (τ.functional p).re| +
          2 * (3 * η * ((τ.functional y).re + c * (τ.functional p).re) +
            4 * |(τ.functional y).re - c * (τ.functional p).re|) := by gcongr
      _ = _ := by ring

namespace ProjectionRow

variable {I : Type uI} [Fintype I] {q : D} (U : ProjectionRow I q)

omit [StarOrderedRing D] in
lemma trace_matrix_proportion (τ : TracialState D) {e : D} (heq : e * q = e)
    (s : Matrix I I ℂ) :
    τ.functional (U.matrix e s) * τ.functional (U.sample q) =
      τ.functional (U.matrix q s) * τ.functional (U.sample e) := by
  rw [U.trace_matrix τ e heq, U.trace_matrix τ q U.projection.isIdempotentElem,
    U.trace_sample τ e heq, U.trace_sample τ q U.projection.isIdempotentElem]
  ring

theorem matrix_block_sampling {e : D} (he : IsStarProjection e) (heq : e ≤ q)
    (x : unitary D) {η c : ℝ} (hη : η < 1) (hc : 0 ≤ c)
    (happrox : ∃ s : Matrix I I ℂ,
      ‖U.sample q * (x : D) * U.sample q - U.matrix q s‖ < η) (τ : TracialState D) :
    ‖τ.functional (U.sample e * (x : D)) -
        (c : ℂ) * τ.functional (U.sample q * (x : D))‖ ≤
      η * ((τ.functional (U.sample e)).re + c * (τ.functional (U.sample q)).re) +
        2 * |(τ.functional (U.sample e)).re - c * (τ.functional (U.sample q)).re| ∧
    |traceTwoNorm τ ((x : D) * U.sample e - U.sample e * (x : D)) ^ 2 -
        c * traceTwoNorm τ ((x : D) * U.sample q - U.sample q * (x : D)) ^ 2| ≤
      6 * η * ((τ.functional (U.sample e)).re + c * (τ.functional (U.sample q)).re) +
        10 * |(τ.functional (U.sample e)).re - c * (τ.functional (U.sample q)).re| := by
  obtain ⟨s, hs⟩ := happrox
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  have hqe := (he.le_iff_mul_eq_right U.projection).mp heq
  have hq := U.projection.isIdempotentElem
  apply sampling_via_scalar_reference τ U.range_projection (U.sample_projection he hqe)
    (U.sample_le he heq) (U.matrix_sample_commute hq hq s).symm
    (U.matrix_sample_commute hqe heq' s).symm x hη hc hs
  · rw [U.matrix_sample _ _ hqe, hqe, U.matrix_sample _ _ hq, hq]
    exact U.trace_matrix_proportion τ heq' s
  · rw [U.matrix_star, U.projection.isSelfAdjoint.star_eq, U.matrix_mul _ _ hq, hq,
      U.matrix_sample _ _ hqe, hqe, U.matrix_sample _ _ hq, hq]
    exact U.trace_matrix_proportion τ heq' (star s * s)

end ProjectionRow

end SamplingConclusion

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

section SpectralRoot

variable {D : Type uD} [CStarAlgebra D]

variable {I : Type uI} [Fintype I]

variable [PartialOrder D] [StarOrderedRing D]

lemma projection_combination_nonneg (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) : 0 ≤ ∑ i, c i • e i :=
  Finset.sum_nonneg (fun i _ => smul_nonneg (hc i) (he i).nonneg)

end SpectralRoot

end CurrentMain

end

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

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_re_le_oneNorm (τ : Pureness.TracialState D) {a : D} (ha : IsSelfAdjoint a) :
    (τ.functional a).re ≤ traceOneNorm τ a := by
  simpa only [one_mul] using
    trace_selfAdjoint_contraction_mul_le τ (IsSelfAdjoint.one D) ha (IsStarProjection.one D).norm_le

end

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

namespace WeightedBlockFamily

variable {r : D} (F : WeightedBlockFamily r)

omit [StarOrderedRing D] in
lemma range_projection (j : F.Index) : IsStarProjection (F.range j) :=
  (F.row j).range_projection

lemma weightedSum_nonneg : 0 ≤ F.weightedSum :=
  projection_combination_nonneg F.range F.range_projection F.weight
    (fun j => (F.weight_pos j).le)

end WeightedBlockFamily

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I] {q : D}

namespace ProjectionRow

variable (U : ProjectionRow I q)

omit [StarOrderedRing D] in
lemma trace_overlap_sample (τ : Pureness.TracialState D) (z a : D) :
    τ.functional (z * U.sample a) = τ.functional (a * U.overlapTest z) := by
  simp only [sample, coeff, overlapTest, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show z * (U.entry i * a * star (U.entry i)) =
    (z * U.entry i) * (a * star (U.entry i)) by noncomm_ring, τ.tracial]
  congr 1
  noncomm_ring

theorem sample_mass_overlap (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    (z : D) {c ε : ℝ} (hc : c ∈ Set.Icc 0 1) (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ τ : Pureness.TracialState D,
      ‖τ.functional (U.sample e) - (c : ℂ) * τ.functional (U.sample q)‖ < ε ∧
      ‖τ.functional (z * U.sample e) - (c : ℂ) * τ.functional (z * U.sample q)‖ < ε := by
  classical
  let k : ℝ := Fintype.card I
  let δ := ε / (k + 1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (k + 1) = ε := div_mul_cancel₀ _ (ne_of_gt (by positivity))
  have hkδ : k * δ < ε := by nlinarith
  have hδε : δ ≤ ε := by nlinarith
  obtain ⟨e, he, heq, htest⟩ := split_finite_linear_tests hRR hsmall U.projection hc
    {1, U.overlapTest z} hδ
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  refine ⟨e, he, heq, ?_⟩
  intro τ
  constructor
  · have hmass := htest 1 (Finset.mem_insert_self _ _) τ
    simp only [mul_one] at hmass
    rw [U.trace_sample τ e heq', U.trace_sample τ q U.projection.isIdempotentElem]
    rw [show (Fintype.card I : ℂ) * τ.functional e -
      (c : ℂ) * ((Fintype.card I : ℂ) * τ.functional q) =
      (Fintype.card I : ℂ) * (τ.functional e - (c : ℂ) * τ.functional q) by ring,
      norm_mul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hmass.le hk).trans_lt hkδ
  · rw [U.trace_overlap_sample, U.trace_overlap_sample]
    exact (htest _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) τ).trans_le hδε

end ProjectionRow

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sub_le (τ : Pureness.TracialState D) (a b : D) :
    traceTwoNorm τ (a - b) ≤ traceTwoNorm τ a + traceTwoNorm τ b := by
  simpa only [sub_eq_add_neg, traceTwoNorm_neg] using traceTwoNorm_add_le τ a (-b)

lemma traceTwoNorm_commutator_le (τ : Pureness.TracialState D) {x : D} (hx : ‖x‖ ≤ 1) (a : D) :
    traceTwoNorm τ (x * a - a * x) ≤ 2 * traceTwoNorm τ a := by
  have h0 := traceTwoNorm_nonneg τ a
  calc
    _ ≤ traceTwoNorm τ (x * a) + traceTwoNorm τ (a * x) := traceTwoNorm_sub_le τ _ _
    _ ≤ ‖x‖ * traceTwoNorm τ a + ‖x‖ * traceTwoNorm τ a :=
      add_le_add (traceTwoNorm_mul_left τ _ _) (traceTwoNorm_mul_right τ _ _)
    _ ≤ _ := by nlinarith

lemma commutator_perturb_sq (τ : Pureness.TracialState D) {x : D} (hx : ‖x‖ ≤ 1) (t y : D) :
    traceTwoNorm τ (x * t - t * x) ^ 2 ≤
      2 * traceTwoNorm τ (x * y - y * x) ^ 2 + 8 * traceTwoNorm τ (t - y) ^ 2 := by
  have he : x * t - t * x = (x * y - y * x) + (x * (t - y) - (t - y) * x) := by noncomm_ring
  have hb : traceTwoNorm τ (x * t - t * x) ≤
      traceTwoNorm τ (x * y - y * x) + 2 * traceTwoNorm τ (t - y) := by
    rw [he]
    exact (traceTwoNorm_add_le τ _ _).trans
      (add_le_add le_rfl (traceTwoNorm_commutator_le τ hx _))
  have h0 := traceTwoNorm_nonneg τ (x * t - t * x)
  have h1 := traceTwoNorm_nonneg τ (x * y - y * x)
  have h2 := traceTwoNorm_nonneg τ (t - y)
  nlinarith [sq_nonneg (traceTwoNorm τ (x * y - y * x) - 2 * traceTwoNorm τ (t - y))]

lemma projection_overlap_identity (τ : Pureness.TracialState D) {z r : D}
    (hz : IsStarProjection z) (hr : IsStarProjection r) (v : D) :
    (τ.functional (z * (v * r * star v))).re = traceTwoNorm τ (z * v * r) ^ 2 := by
  rw [traceTwoNorm_sq]
  simp only [star_mul, hz.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq,
    mul_assoc, ← mul_assoc z z, hz.isIdempotentElem.eq]
  have he : τ.functional (r * (star v * (z * (v * r)))) =
      τ.functional (z * (v * r * star v)) := by
    calc
      _ = τ.functional ((star v * (z * v)) * (r * r)) := by
        rw [τ.tracial r]
        congr 1
        noncomm_ring
      _ = τ.functional (star v * (z * (v * r))) := by
        rw [hr.isIdempotentElem.eq]
        congr 1
        noncomm_ring
      _ = _ := by
        rw [τ.tracial (star v)]
        congr 1
        noncomm_ring
  simpa only [mul_assoc] using congrArg Complex.re he.symm

lemma weightedAverage_overlap {I : Type uI} [Fintype I]
    (τ : Pureness.TracialState D) (w : I → ℝ) (v : I → D)
    {z r : D} (hz : IsStarProjection z) (hr : IsStarProjection r) :
    (τ.functional (z * weightedAverage w v r)).re =
      ∑ i, w i * traceTwoNorm τ (z * v i * r) ^ 2 := by
  simp only [weightedAverage, Finset.mul_sum, mul_smul_comm, map_sum,
    τ.functional.map_smul_of_tower, Complex.re_sum, Complex.smul_re, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (w i * ·) (projection_overlap_identity τ hz hr (v i))

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.OrthogonalPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma projection_orthogonal_of_le_complement {t z : D}
    (ht : IsStarProjection t) (hz : IsStarProjection z) (hle : t ≤ 1 - z) : t * z = 0 := by
  have h := (ht.le_iff_mul_eq_left hz.one_sub).mp hle
  rw [mul_sub, mul_one] at h
  exact sub_eq_self.mp h

namespace ProjectionInsertion

variable {n : ℕ} {z₀ : D} (S : ProjectionInsertion n z₀)

lemma monotone : Monotone S.occupied := by
  apply Fin.monotone_iff_le_succ.mpr
  intro a
  rw [S.update a]
  exact le_add_of_nonneg_right (S.inserted_projection a).nonneg

lemma inserted_le_next (a : Fin n) : S.inserted a ≤ S.occupied a.succ := by
  rw [S.update a]
  exact le_add_of_nonneg_left (S.occupied_projection a.castSucc).nonneg

lemma inserted_occupied_orthogonal (a : Fin n) : S.inserted a * S.occupied a.castSucc = 0 :=
  projection_orthogonal_of_le_complement (S.inserted_projection a)
    (S.occupied_projection a.castSucc) (S.complement a)

lemma orthogonal : Pairwise (fun a b => S.inserted a * S.inserted b = 0) := by
  have hef (a b : Fin n) (hab : a < b) : S.inserted b * S.inserted a = 0 := by
    have hle : S.inserted a ≤ S.occupied b.castSucc :=
      (S.inserted_le_next a).trans (S.monotone (Fin.succ_le_castSucc_iff.mpr hab))
    have hs := ((S.inserted_projection a).le_iff_mul_eq_right
      (S.occupied_projection b.castSucc)).mp hle
    rw [← hs, ← mul_assoc, S.inserted_occupied_orthogonal b, zero_mul]
  intro a b hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact projection_mul_zero_symm (S.inserted_projection b) (S.inserted_projection a) (hef a b hab)
  · exact hef b a hba

lemma final_eq : S.occupied (Fin.last n) = z₀ + ∑ a, S.inserted a := by
  have hu : ∑ a : Fin n, S.occupied a.succ =
      (∑ a : Fin n, S.occupied a.castSucc) + ∑ a, S.inserted a := by
    simp_rw [S.update]
    exact Finset.sum_add_distrib
  have h₁ := Fin.sum_univ_succ S.occupied
  have h₂ := Fin.sum_univ_castSucc S.occupied
  have he : S.occupied (Fin.last n) + (∑ a : Fin n, S.occupied a.castSucc) =
      (z₀ + ∑ a, S.inserted a) + (∑ a : Fin n, S.occupied a.castSucc) := by
    calc
      _ = ∑ a, S.occupied a := by simpa only [add_comm] using h₂.symm
      _ = S.occupied 0 + ∑ a : Fin n, S.occupied a.succ := h₁
      _ = _ := by rw [S.initial, hu]; abel
  exact add_right_cancel he

lemma initial_orthogonal (a : Fin n) : z₀ * S.inserted a = 0 := by
  have hp₀ : IsStarProjection z₀ := by simpa only [S.initial] using S.occupied_projection 0
  have hsub₀ := ((S.occupied_projection 0).le_iff_mul_eq_right
    (S.occupied_projection a.castSucc)).mp (S.monotone (Fin.zero_le _))
  have hsub : S.occupied a.castSucc * z₀ = z₀ := by simpa only [S.initial] using hsub₀
  have hzi : S.inserted a * z₀ = 0 := by
    calc
      _ = S.inserted a * (S.occupied a.castSucc * z₀) := congrArg (S.inserted a * ·) hsub.symm
      _ = 0 := by rw [← mul_assoc, S.inserted_occupied_orthogonal a, zero_mul]
  exact projection_mul_zero_symm (S.inserted_projection a) hp₀ hzi

end ProjectionInsertion

lemma exists_projection_insertion (n : ℕ) {z₀ : D} (hz₀ : IsStarProjection z₀)
    (Q : Fin n → D → D → D → Prop)
    (hstep : ∀ a z, IsStarProjection z → ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧
      t ≤ 1 - z ∧ Q a z y t) :
    ∃ S : ProjectionInsertion n z₀, ∀ a,
      Q a (S.occupied a.castSucc) (S.sampled a) (S.inserted a) := by
  induction n generalizing z₀ with
  | zero =>
    refine ⟨⟨fun _ => z₀, Fin.elim0, Fin.elim0, rfl, fun _ => hz₀,
      (fun a => Fin.elim0 a), (fun a => Fin.elim0 a), (fun a => Fin.elim0 a),
      (fun a => Fin.elim0 a)⟩, (fun a => Fin.elim0 a)⟩
  | succ n ih =>
    obtain ⟨y, t, hy, ht, htz, hQ⟩ := hstep 0 z₀ hz₀
    have hzt : z₀ * t = 0 := projection_mul_zero_symm ht hz₀
      (projection_orthogonal_of_le_complement ht hz₀ htz)
    obtain ⟨S, hS⟩ := ih (hz₀.add ht hzt) (fun a => Q a.succ)
      (fun a => hstep a.succ)
    let R : ProjectionInsertion (n + 1) z₀ := {
      occupied := Fin.cons z₀ S.occupied
      sampled := Fin.cons y S.sampled
      inserted := Fin.cons t S.inserted
      initial := rfl
      occupied_projection := Fin.cases hz₀ S.occupied_projection
      sampled_projection := Fin.cases hy S.sampled_projection
      inserted_projection := Fin.cases ht S.inserted_projection
      complement := by
        intro a
        cases a using Fin.cases with
        | zero => exact htz
        | succ a => exact S.complement a
      update := by
        intro a
        cases a using Fin.cases with
        | zero => exact S.initial
        | succ a => exact S.update a }
    refine ⟨R, ?_⟩
    intro a
    cases a using Fin.cases with
    | zero => exact hQ
    | succ a => exact hS a

lemma re_difference_le_of_complex {a b : ℂ} {c ε : ℝ}
    (h : ‖a - (c : ℂ) * b‖ ≤ ε) : |a.re - c * b.re| ≤ ε := by
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using (Complex.abs_re_le_norm (a - (c : ℂ) * b)).trans h

lemma exists_packing_step {I : Type uI} [Fintype I] {q z : D} (U : ProjectionRow I q)
    (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    (hz : IsStarProjection z) (K : Finset (unitary D)) {c η ε : ℝ}
    (hc : c ∈ Set.Icc 0 1) (hη : η < 1) (hε : 0 < ε)
    (happrox : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ‖U.sample q * (x : D) * U.sample q - U.matrix q H‖ < η) :
    ∃ y t : D, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1 - z ∧
      PackingStepBounds (U.sample q) z y t c η ε K := by
  obtain ⟨e, he, heq, hs⟩ := U.sample_mass_overlap hRR hsmall z hc hε
  let y := U.sample e
  have hy : IsStarProjection y := U.sample_projection he
    ((he.le_iff_mul_eq_right U.projection).mp heq)
  obtain ⟨t, ht, htz, hmove⟩ := orthogonal_insertion hRR hz hy
  have hm (τ : Pureness.TracialState D) :
      |(τ.functional y).re - c * (τ.functional (U.sample q)).re| ≤ ε :=
    re_difference_le_of_complex (hs τ).1.le
  refine ⟨y, t, hy, ht, htz, {
    mass := hm
    overlap := fun τ => re_difference_le_of_complex (hs τ).2.le
    inserted_mass_lower := ?_
    inserted_mass_upper := fun τ => (hmove τ).1.2
    inserted_distance := ?_
    inserted_linear := fun τ => (hmove τ).2.2
    sampled_linear := ?_
    sampled_energy := ?_ }⟩
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).1.1
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).2.1
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).1
    exact hb.trans (by dsimp [y] at hm ⊢; linarith [hm τ])
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).2
    have hb' := (abs_le.mp hb).2
    dsimp [y] at hm ⊢
    linarith [hm τ]

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {r : D}

omit [StarOrderedRing D] in
lemma signed_weighted_sum (F : WeightedBlockFamily r) (η : ℝ) (f : F.Index → ℝ) :
    (∑ a : F.Index × Bool, (η * F.weight a.1 / 2) * f a.1) =
      η * ∑ j, F.weight j * f j := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool]
  ring

namespace SampledPackingRound

variable {F : WeightedBlockFamily r} {z₀ : D} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

omit [StarOrderedRing D] in
lemma sampledMass_error (τ : Pureness.TracialState D) :
    |R.sampledMass τ - R.targetMass τ| ≤ R.totalError := by
  rw [sampledMass, targetMass, ← signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |(τ.functional (R.sampled a)).re -
        (η * F.weight a.1 / 2) * (τ.functional (F.range a.1)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : F.Index × Bool, δ := Finset.sum_le_sum fun a _ => (R.bounds a).mass τ
    _ = R.totalError := by simp [totalError, nsmul_eq_mul]

omit [StarOrderedRing D] in
lemma insertedMass_bounds (τ : Pureness.TracialState D) :
    R.sampledMass τ - 3 * R.overlap τ ≤
      (τ.functional R.final).re - (τ.functional z₀).re ∧
    (τ.functional R.final).re - (τ.functional z₀).re ≤ R.sampledMass τ := by
  have hm : (τ.functional R.final).re - (τ.functional z₀).re =
      ∑ a, (τ.functional (R.inserted a)).re := by
    rw [R.final_eq, map_add, map_sum, Complex.add_re, Complex.re_sum]
    abel
  rw [hm]
  constructor
  · have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_mass_lower τ
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sampledMass, overlap] using h
  · exact Finset.sum_le_sum fun a _ => (R.bounds a).inserted_mass_upper τ

lemma initial_le_final : z₀ ≤ R.final := by
  conv_rhs => rw [R.final_eq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => (R.inserted_projection a).nonneg)

lemma overlap_le_target (τ : Pureness.TracialState D) (hη : 0 ≤ η) :
    R.overlap τ ≤ R.totalError + η * ∑ j, F.weight j * (τ.functional (R.final * F.range j)).re := by
  have hb (a : F.Index × Bool) : (τ.functional (R.occupied a * R.sampled a)).re ≤
      (η * F.weight a.1 / 2) * (τ.functional (R.final * F.range a.1)).re + δ := by
    have h := (abs_le.mp ((R.bounds a).overlap τ)).2
    have hm := trace_mul_mono_left τ (F.range_projection a.1).nonneg (R.occupied_le_final a)
    have hc : 0 ≤ η * F.weight a.1 / 2 := by
      have hw := F.weight_pos a.1
      positivity
    nlinarith
  calc
    _ ≤ ∑ a, ((η * F.weight a.1 / 2) * (τ.functional (R.final * F.range a.1)).re + δ) :=
      Finset.sum_le_sum fun a _ => hb a
    _ = _ := by
      rw [Finset.sum_add_distrib, signed_weighted_sum F η (fun j => (τ.functional (R.final * F.range j)).re)]
      simp [totalError, nsmul_eq_mul, add_comm]

omit [StarOrderedRing D] in
lemma sampled_linear_sum (τ : Pureness.TracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, ‖τ.functional (R.sampled a * (x : D)) -
      ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) ≤
      η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).sampled_linear x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sampledMass, targetMass, totalError]
  rw [signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

omit [StarOrderedRing D] in
lemma sampled_energy_sum (τ : Pureness.TracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, traceTwoNorm τ ((x : D) * R.sampled a - R.sampled a * (x : D)) ^ 2) ≤
      η * ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 +
      6 * η * (R.sampledMass τ + R.targetMass τ) + 10 * R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).sampled_energy x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sampledMass, targetMass, totalError]
  rw [signed_weighted_sum F η (fun j => traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2),
    signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

lemma inserted_energy_sum (τ : Pureness.TracialState D) (x : unitary D) :
    (∑ a, traceTwoNorm τ ((x : D) * R.inserted a - R.inserted a * (x : D)) ^ 2) ≤
      2 * ∑ a, traceTwoNorm τ ((x : D) * R.sampled a - R.sampled a * (x : D)) ^ 2 +
        40 * R.overlap τ := by
  have hx : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have he := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    commutator_perturb_sq τ hx (R.inserted a) (R.sampled a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hd he
  dsimp [overlap]
  linarith

end SampledPackingRound

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

lemma trace_projected_mass_perturb (τ : Pureness.TracialState D) {p b h : D}
    (hp : IsStarProjection p) (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) {ε : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε) :
    (τ.functional (p * b)).re ≤ (τ.functional (p * h)).re + ε := by
  have ht := (trace_selfAdjoint_contraction_mul_le τ hp.isSelfAdjoint (hb.sub hh) hp.norm_le).trans hclose
  simp only [mul_sub, map_sub, Complex.sub_re] at ht
  linarith

namespace WeightedBlockFamily

variable {r : D} (F : WeightedBlockFamily r)

omit [StarOrderedRing D] in
lemma trace_weightedSum (τ : Pureness.TracialState D) :
    (τ.functional F.weightedSum).re = ∑ j, F.weight j * (τ.functional (F.range j)).re := by
  simp only [weightedSum, map_sum, τ.functional.map_smul_of_tower, Complex.re_sum,
    Complex.smul_re, smul_eq_mul]

omit [StarOrderedRing D] in
lemma trace_mul_weightedSum (τ : Pureness.TracialState D) (z : D) :
    (τ.functional (z * F.weightedSum)).re =
      ∑ j, F.weight j * (τ.functional (z * F.range j)).re := by
  simp only [weightedSum, Finset.mul_sum, mul_smul_comm, map_sum,
    τ.functional.map_smul_of_tower, Complex.re_sum, Complex.smul_re, smul_eq_mul]

end WeightedBlockFamily

namespace SampledPackingRound

variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

omit [StarOrderedRing D] in
lemma targetMass_eq (τ : Pureness.TracialState D) :
    R.targetMass τ = η * (τ.functional F.weightedSum).re := by
  rw [targetMass, F.trace_weightedSum]

lemma estimates_of_average (hz₀ : IsStarProjection z₀) (hη : 0 < η) (hη1 : η < 1)
    {E : ℝ} (hE : 0 ≤ E) {b : D} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (herror : R.totalError ≤ η ^ 2)
    (hmass : ∀ τ : Pureness.TracialState D,
      (τ.functional (1 - z₀)).re - η ^ 2 ≤ (τ.functional b).re ∧
      (τ.functional b).re ≤ (τ.functional (1 - z₀)).re)
    (hclose : ∀ τ : Pureness.TracialState D, traceOneNorm τ (F.weightedSum - b) ≤ η ^ 2)
    (henergy : ∀ x : unitary D, x ∈ K → ∀ τ : Pureness.TracialState D,
      ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 ≤ 6 * η)
    (hold : ∀ τ : Pureness.TracialState D, (τ.functional (z₀ * b)).re ≤ 4 * E) : R.Estimates E := by
  have hηsq : η ^ 2 ≤ η := by nlinarith
  have hηcube : η ^ 3 ≤ η ^ 2 := by nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hη1.le)]
  have hc (τ : Pureness.TracialState D) :
      η * (τ.functional (1 - z₀)).re - 2 * η ^ 3 ≤ R.targetMass τ ∧ R.targetMass τ ≤ 2 * η := by
    have herr := (trace_mass_difference_abs_le τ
      (F.weightedSum_nonneg.isSelfAdjoint.sub hb.isSelfAdjoint)).trans (hclose τ)
    simp only [map_sub, Complex.sub_re] at herr
    obtain ⟨hl, hu⟩ := abs_le.mp herr
    have hbnds := hmass τ
    have hr := trace_projection_le_one τ hz₀.one_sub
    rw [R.targetMass_eq τ]
    constructor <;> nlinarith
  have hy (τ : Pureness.TracialState D) :
      η * (τ.functional (1 - z₀)).re - 3 * η ^ 2 ≤ R.sampledMass τ ∧ R.sampledMass τ ≤ 3 * η := by
    have herr := abs_le.mp ((R.sampledMass_error τ).trans herror)
    have ht := hc τ
    constructor <;> nlinarith
  have hl (τ : Pureness.TracialState D) : R.overlap τ ≤ 4 * η * E + 5 * η ^ 2 := by
    have hh := trace_projected_mass_perturb τ R.final_projection F.weightedSum_nonneg.isSelfAdjoint
      hb.isSelfAdjoint (hclose τ)
    rw [F.trace_mul_weightedSum] at hh
    have hdiff : 0 ≤ R.final - z₀ := sub_nonneg.mpr R.initial_le_final
    have hm := trace_mul_mono_right τ hdiff hb1
    simp only [mul_one, sub_mul, map_sub, Complex.sub_re] at hm
    have him := (R.insertedMass_bounds τ).2
    have ha := R.overlap_le_target τ hη.le
    have hY := (hy τ).2
    nlinarith [hold τ]
  have hincr (τ : Pureness.TracialState D) : R.overlap τ ≤ 1000 * η * (E + η) := by
    have hηE : 0 ≤ η * E := mul_nonneg hη.le hE
    nlinarith [hl τ, sq_nonneg η]
  refine {
    target_upper := fun τ => (hc τ).2
    sampled_upper := fun τ => (hy τ).2
    sampled_lower := fun τ => (hy τ).1
    overlap_upper := hl
    overlap_incr := hincr
    linear_sum := ?_
    inserted_energy := ?_
    remaining := ?_ }
  · intro x hx τ
    have hs := R.sampled_linear_sum τ x hx
    have hY := (hy τ).2
    have hC := (hc τ).2
    nlinarith
  · intro x hx τ
    have hs := R.sampled_energy_sum τ x hx
    have ht := R.inserted_energy_sum τ x
    have hY := (hy τ).2
    have hC := (hc τ).2
    have hB := henergy x hx τ
    have hL := hl τ
    have hηE : 0 ≤ η * E := mul_nonneg hη.le hE
    nlinarith
  · intro τ
    have hm := (R.insertedMass_bounds τ).1
    have hY := (hy τ).1
    simp only [map_sub, τ.normalized, Complex.sub_re, Complex.one_re] at hY ⊢
    nlinarith

end SampledPackingRound

lemma signed_sum {I : Type uI} {M : Type uM} [Fintype I] [AddCommMonoid M] (f : I × Bool → M) :
    ∑ a, f a = (∑ j, f (j, false)) + ∑ j, f (j, true) := by
  simp [Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

lemma paired_sum_norm_sub_le {I : Type uI} [Fintype I] (f : I × Bool → ℂ) (t : I → ℂ) :
    ‖(∑ j, f (j, false)) - ∑ j, f (j, true)‖ ≤ ∑ a, ‖f a - t a.1‖ := by
  calc
    _ = ‖(∑ j, (f (j, false) - t j)) - ∑ j, (f (j, true) - t j)‖ := by
      simp only [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ ‖∑ j, (f (j, false) - t j)‖ + ‖∑ j, (f (j, true) - t j)‖ := norm_sub_le _ _
    _ ≤ (∑ j, ‖f (j, false) - t j‖) + ∑ j, ‖f (j, true) - t j‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = _ := (signed_sum (fun a => ‖f a - t a.1‖)).symm

namespace SampledPackingRound

section

variable {r z₀ : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

omit [StarOrderedRing D] in
lemma final_eq_signSum : R.final = z₀ + (R.signSum false + R.signSum true) := by
  rw [R.final_eq, signed_sum]
  rfl

lemma signSum_energy (τ : Pureness.TracialState D) (x : D) :
    traceTwoNorm τ (x * R.signSum false - R.signSum false * x) ^ 2 +
      traceTwoNorm τ (x * R.signSum true - R.signSum true * x) ^ 2 ≤
      ∑ a, traceTwoNorm τ (x * R.inserted a - R.inserted a * x) ^ 2 := by
  rw [signed_sum]
  apply add_le_add
  all_goals
    exact (orthogonal_sum_energy_le Finset.univ _ (fun _ _ => R.inserted_projection _)
      (fun _ _ _ _ h => R.inserted_orthogonal (fun he => h (Prod.mk.inj he).1)) τ x).2

lemma displacement_sum_le (τ : Pureness.TracialState D) (x : D) (hx : ‖x‖ ≤ 1) :
    (∑ a, ‖τ.functional ((R.inserted a - R.sampled a) * x)‖) ≤
      2 * Real.sqrt (R.sampledMass τ) * Real.sqrt (5 * R.overlap τ) := by
  have hs (a : F.Index × Bool) : 0 ≤ (τ.functional (R.sampled a)).re :=
    (τ.functional.map_nonneg (R.sampled_projection a).nonneg).1
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (F.Index × Bool))
    (fun a => Real.sqrt (τ.functional (R.sampled a)).re)
    (fun a => traceTwoNorm τ (R.inserted a - R.sampled a))
  simp only [Real.sq_sqrt (hs _)] at hcs
  calc
    _ ≤ ∑ a, 2 * Real.sqrt (τ.functional (R.sampled a)).re *
        traceTwoNorm τ (R.inserted a - R.sampled a) :=
      Finset.sum_le_sum fun a _ => (R.bounds a).inserted_linear τ x hx
    _ = 2 * ∑ a, Real.sqrt (τ.functional (R.sampled a)).re *
        traceTwoNorm τ (R.inserted a - R.sampled a) := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ 2 * (Real.sqrt (R.sampledMass τ) *
        Real.sqrt (∑ a, traceTwoNorm τ (R.inserted a - R.sampled a) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      simpa only [← Finset.mul_sum, overlap] using hd

lemma signSum_balance (τ : Pureness.TracialState D) (x : unitary D) (hx : x ∈ K) :
    ‖τ.functional (R.signSum false * (x : D)) - τ.functional (R.signSum true * (x : D))‖ ≤
      η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError +
        2 * Real.sqrt (R.sampledMass τ) * Real.sqrt (5 * R.overlap τ) := by
  have hxu : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have h := paired_sum_norm_sub_le
    (fun a : F.Index × Bool => τ.functional (R.inserted a * (x : D)))
    (fun j => ((η * F.weight j / 2 : ℝ) : ℂ) * τ.functional (F.range j * (x : D)))
  simp only [signSum, Finset.sum_mul, map_sum]
  apply h.trans
  calc
    _ ≤ (∑ a, ‖τ.functional (R.sampled a * (x : D)) -
        ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) +
        ∑ a, ‖τ.functional ((R.inserted a - R.sampled a) * (x : D))‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      have he : τ.functional (R.inserted a * (x : D)) -
          ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D)) =
          (τ.functional (R.sampled a * (x : D)) -
          ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))) +
          τ.functional ((R.inserted a - R.sampled a) * (x : D)) := by
        simp only [sub_mul, map_sub]; abel
      rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (R.sampled_linear_sum τ x hx) (R.displacement_sum_le τ _ hxu)

end

variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

lemma Estimates.balance {E : ℝ} (H : R.Estimates E) (hη : 0 < η)
    (herror : R.totalError ≤ η ^ 2) (τ : Pureness.TracialState D)
    (x : unitary D) (hx : x ∈ K) :
    ‖τ.functional (R.signSum false * (x : D)) - τ.functional (R.signSum true * (x : D))‖ ≤
      7 * η ^ 2 + 2 * η * Real.sqrt (60 * E + 75 * η) := by
  have hid : Real.sqrt (3 * η) * Real.sqrt (5 * (4 * η * E + 5 * η ^ 2)) =
      η * Real.sqrt (60 * E + 75 * η) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 * η)]
    rw [show 3 * η * (5 * (4 * η * E + 5 * η ^ 2)) = η ^ 2 * (60 * E + 75 * η) by ring]
    rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]
  apply (R.signSum_balance τ x hx).trans
  have hlin : η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError ≤ 7 * η ^ 2 := by
    nlinarith [H.sampled_upper τ, H.target_upper τ]
  calc
    _ ≤ 7 * η ^ 2 + 2 * Real.sqrt (3 * η) * Real.sqrt (5 * (4 * η * E + 5 * η ^ 2)) := by
      apply add_le_add hlin
      gcongr
      · exact H.sampled_upper τ
      · exact H.overlap_upper τ
    _ = _ := by rw [mul_assoc, hid, ← mul_assoc]

end SampledPackingRound

namespace OrthogonalProjectionPair

variable (Q : OrthogonalProjectionPair D)

lemma total_energy_le (τ : Pureness.TracialState D) (x : D) :
    traceTwoNorm τ (x * Q.total - Q.total * x) ^ 2 ≤ Q.energy τ x :=
  orthogonal_pair_energy_le τ Q.left_projection Q.right_projection Q.orthogonal x

variable {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F Q.total K η δ)

lemma appendRound_total : (Q.appendRound R).total = R.final := by
  rw [R.final_eq_signSum]
  dsimp [appendRound, total]
  abel

lemma appendRound_energy (τ : Pureness.TracialState D) (x : D) :
    (Q.appendRound R).energy τ x ≤ Q.energy τ x +
      ∑ a, traceTwoNorm τ (x * R.inserted a - R.inserted a * x) ^ 2 := by
  have hp := orthogonal_pair_energy_le τ Q.left_projection (R.signSum_projection false)
    (Q.left_signSum_orthogonal R false) x
  have hs := orthogonal_pair_energy_le τ Q.right_projection (R.signSum_projection true)
    (Q.right_signSum_orthogonal R true) x
  have hr := R.signSum_energy τ x
  dsimp [energy, appendRound]
  linarith

lemma appendRound_balance (τ : Pureness.TracialState D) (x : D) :
    (Q.appendRound R).balance τ x ≤ Q.balance τ x +
      ‖τ.functional (R.signSum false * x) - τ.functional (R.signSum true * x)‖ := by
  dsimp [balance, appendRound]
  simp only [add_mul, map_add]
  calc
    _ = ‖(τ.functional (Q.left * x) - τ.functional (Q.right * x)) +
          (τ.functional (R.signSum false * x) - τ.functional (R.signSum true * x))‖ := by
      congr 1; abel
    _ ≤ _ := norm_add_le _ _

end OrthogonalProjectionPair

end

lemma packingEnergy_nonneg {η : ℝ} (hη : 0 ≤ η) (n : ℕ) : 0 ≤ packingEnergy η n := by
  apply mul_nonneg hη
  exact sub_nonneg.mpr
    (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg (by norm_num) hη)))

lemma packingEnergy_succ (η : ℝ) (n : ℕ) :
    packingEnergy η (n + 1) = packingEnergy η n + 1000 * η * (packingEnergy η n + η) := by
  simp only [packingEnergy, pow_succ]
  ring

lemma packingEnergy_mono {η : ℝ} (hη : 0 ≤ η) : Monotone (packingEnergy η) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [packingEnergy_succ]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (add_nonneg (packingEnergy_nonneg hη n) hη))

lemma packingRemainder_step {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    (1 - η) * packingRemainder η n + 3 * η ^ 2 +
      3 * (1000 * η * (packingEnergy η n + η)) ≤ packingRemainder η (n + 1) := by
  have hE := packingEnergy_nonneg hη n
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 ≤ η * (3 * n * η ^ 2 + 3 * packingEnergy η n) := by positivity
  simp only [packingRemainder, packingEnergy_succ, Nat.cast_add, Nat.cast_one, pow_succ]
  nlinarith

lemma packingBalance_step {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    packingBalance η n + (7 * η ^ 2 + 2 * η * Real.sqrt (60 * packingEnergy η n + 75 * η)) ≤
      packingBalance η (n + 1) := by
  have hE := packingEnergy_mono hη (Nat.le_succ n)
  simp only [packingBalance, Nat.cast_add, Nat.cast_one]
  calc
    _ = (n + 1 : ℝ) * (7 * η ^ 2 + 2 * η * Real.sqrt (60 * packingEnergy η n + 75 * η)) := by ring
    _ ≤ _ := by gcongr

lemma packingEnergy_exp_bound {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    packingEnergy η n ≤ η * Real.exp (1000 * (n * η)) := by
  have hp : (1 + 1000 * η) ^ n ≤ Real.exp (1000 * η) ^ n := by
    gcongr
    simpa only [add_comm (1000 * η) 1] using Real.add_one_le_exp (1000 * η)
  rw [← Real.exp_nat_mul] at hp
  dsimp [packingEnergy]
  apply mul_le_mul_of_nonneg_left _ hη
  have he : (n : ℝ) * (1000 * η) = 1000 * (n * η) := by ring
  rw [he] at hp
  linarith

lemma packing_decay_exp_bound {η : ℝ} (hη1 : η ≤ 1) (n : ℕ) :
    (1 - η) ^ n ≤ Real.exp (-((n : ℝ) * η)) := by
  have hp : (1 - η) ^ n ≤ (Real.exp (-η)) ^ n := by
    apply pow_le_pow_left₀ (sub_nonneg.mpr hη1)
    have h := Real.add_one_le_exp (-η)
    linarith
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_neg] using hp

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.FinitePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]

variable [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sub_swap (τ : Pureness.TracialState D) (a b : D) :
    traceTwoNorm τ (a - b) = traceTwoNorm τ (b - a) := by
  calc
    _ = traceTwoNorm τ (-(b - a)) := by rw [neg_sub]
    _ = _ := traceTwoNorm_neg τ _

end

section

open Filter Topology

lemma exists_packing_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, ∃ n : ℕ, 0 < η ∧ η < 1 ∧
      Real.sqrt (packingEnergy η n) < ε ∧
      (packingRemainder η n + packingBalance η n) / 2 < ε := by
  have hevent : ∀ᶠ H : ℝ in atTop, Real.exp (-H) < ε :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hε)
  obtain ⟨H, hH, hdecay⟩ := (eventually_gt_atTop (0 : ℝ) |>.and hevent).exists
  let C : ℝ := Real.exp (1000 * H)
  have hC : 0 < C := Real.exp_pos _
  have ht : Tendsto (fun n : ℕ => H / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat H
  have hb : Tendsto (fun n : ℕ => Real.exp (-H) + 3 * H * (H / (n : ℝ)) +
      3 * (H / (n : ℝ)) * C + H * (7 * (H / (n : ℝ)) +
      2 * Real.sqrt (60 * ((H / (n : ℝ)) * C) + 75 * (H / (n : ℝ)))))
      atTop (𝓝 (Real.exp (-H))) := by
    convert ((tendsto_const_nhds.add (ht.const_mul (3 * H))).add
      ((ht.const_mul 3).mul_const C)).add
      (((ht.const_mul 7).add (((ht.mul_const C).const_mul 60 |>.add (ht.const_mul 75)).sqrt.const_mul 2)).const_mul H) using 1
    simp
  have he : Tendsto (fun n : ℕ => Real.sqrt ((H / (n : ℝ)) * C)) atTop (𝓝 0) := by
    simpa using (ht.mul_const C).sqrt
  have hn1 : ∀ᶠ n : ℕ in atTop, H / (n : ℝ) < 1 := ht.eventually (gt_mem_nhds (by norm_num))
  have hne : ∀ᶠ n : ℕ in atTop, Real.sqrt ((H / (n : ℝ)) * C) < ε :=
    he.eventually (gt_mem_nhds hε)
  have hnb := hb.eventually (gt_mem_nhds (show Real.exp (-H) < 2 * ε by linarith))
  obtain ⟨n, hn, hη1, hE, hRB⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and (hn1.and (hne.and hnb))).exists
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let η : ℝ := H / (n : ℝ)
  have hη : 0 < η := div_pos hH hnpos
  have htime : (n : ℝ) * η = H := by dsimp [η]; field_simp
  have hEb : packingEnergy η n ≤ η * C := by
    simpa only [htime] using packingEnergy_exp_bound hη.le n
  have hRb : packingRemainder η n ≤ Real.exp (-H) + 3 * H * η + 3 * η * C := by
    have hd := packing_decay_exp_bound hη1.le n
    rw [htime] at hd
    dsimp [packingRemainder]
    calc
      _ ≤ Real.exp (-H) + 3 * n * η ^ 2 + 3 * (η * C) := by gcongr
      _ = _ := by rw [← htime]; ring
  have hBb : packingBalance η n ≤ H * (7 * η + 2 * Real.sqrt (60 * (η * C) + 75 * η)) := by
    dsimp [packingBalance]
    calc
      _ ≤ (n : ℝ) * (7 * η ^ 2 + 2 * η * Real.sqrt (60 * (η * C) + 75 * η)) := by gcongr
      _ = _ := by rw [← htime]; ring
  refine ⟨η, n, hη, hη1, (Real.sqrt_le_sqrt hEb).trans_lt hE, ?_⟩
  have hsum := add_le_add hRb hBb
  change _ < 2 * ε at hRB
  linarith

end

section

open scoped ComplexOrder

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]

variable [PartialOrder D] [StarOrderedRing D]

lemma OrthogonalProjectionPair.halving_le (Q : OrthogonalProjectionPair D)
    (τ : Pureness.TracialState D) (x : unitary D) :
    ‖τ.functional (Q.left * (x : D)) - (1 / 2 : ℂ) * τ.functional (x : D)‖ ≤
      (Q.remaining τ + Q.balance τ (x : D)) / 2 := by
  have hid : τ.functional (Q.left * (x : D)) - (1 / 2 : ℂ) * τ.functional (x : D) =
      (1 / 2 : ℂ) * ((τ.functional (Q.left * (x : D)) - τ.functional (Q.right * (x : D))) -
        τ.functional ((1 - Q.total) * (x : D))) := by
    simp only [total, sub_mul, one_mul, add_mul, map_sub, map_add]
    ring
  have hxu : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have hr := trace_norm_projection_mul_le τ Q.total_projection.one_sub (x : D)
  have hrem : 0 ≤ Q.remaining τ := Complex.nonneg_iff.mp
    (τ.functional.map_nonneg Q.total_projection.one_sub.nonneg) |>.1
  have hr' : ‖τ.functional ((1 - Q.total) * (x : D))‖ ≤ Q.remaining τ := by
    apply hr.trans
    exact (mul_le_mul_of_nonneg_right hxu hrem).trans_eq (one_mul _)
  rw [hid, norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    _ ≤ (1 / 2 : ℝ) * (Q.balance τ (x : D) + Q.remaining τ) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add le_rfl hr')
    _ = _ := by ring

end

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.NuclearTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR uS


section

noncomputable section

universe v

namespace Pureness

namespace CStarAlgebraNorm

variable {R : Type uR} {S : Type uS} [Ring R] [StarRing R] [Algebra ℂ R]
  [Ring S] [StarRing S] [Algebra ℂ S]

lemma comapEquiv_injective (e : R ≃⋆ₐ[ℂ] S) :
    Function.Injective (fun p : CStarAlgebraNorm S => p.comapEquiv e) := by
  intro p q h
  have he : p.toAlgebraNorm = q.toAlgebraNorm := by
    apply AlgebraNorm.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    exact congrArg (fun t : CStarAlgebraNorm R => t.toAlgebraNorm x) h
  cases p
  cases q
  cases he
  rfl

end CStarAlgebraNorm

open scoped TensorProduct

theorem IsNuclear.small {A : Type} [CStarAlgebra A] (hA : IsNuclear.{0,v} A) :
    IsNuclear.{0,0} A := by
  intro B instB
  let E : A ⊗[ℂ] ULift.{v} B ≃ₐ[ℂ] A ⊗[ℂ] B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[ℂ] A) ULift.algEquiv
  have hstar : ∀ x, E (star x) = star (E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | (rw [UniformSpace.Completion.coe_zero]; exact zero_mem _) | simp
    | tmul a b => rfl
    | add x y hx hy => simp only [star_add,map_add,hx,hy]
  let e : A ⊗[ℂ] ULift.{v} B ≃⋆ₐ[ℂ] A ⊗[ℂ] B := StarAlgEquiv.ofAlgEquiv E hstar
  exact ⟨fun p q => CStarAlgebraNorm.comapEquiv_injective e ((hA (ULift.{v} B)).elim _ _)⟩

end Pureness

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

end KrausFamily

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

lemma sum_mul_energy (V : BistochasticTest D) (τ : TracialState D) (d : D) :
    (∑ i, traceTwoNorm τ (V.coeff i*d)^2) = traceTwoNorm τ d^2 := by
  simp only [traceTwoNorm_sq,star_mul,mul_assoc,← Complex.re_sum,← map_sum]
  congr 2
  simp only [← mul_assoc (star (V.coeff _)) _ _,← Finset.sum_mul,← Finset.mul_sum,V.col,one_mul]

lemma sum_energy_mul (V : BistochasticTest D) (τ : TracialState D) (d : D) :
    (∑ i, traceTwoNorm τ (d*V.coeff i)^2) = traceTwoNorm τ d^2 := by
  simp only [traceTwoNorm_sq,star_mul]
  have he (i : Fin V.size) :
      τ.functional (star (V.coeff i)*star d*(d*V.coeff i)) =
        τ.functional (star d*d*(V.coeff i*star (V.coeff i))) := by
    rw [mul_assoc,τ.tracial (star (V.coeff i))]
    congr 1
    noncomm_ring
  simp_rw [he]
  rw [← Complex.re_sum,← map_sum,← Finset.mul_sum,V.row,mul_one]

lemma square_add_le (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a+b)^2 ≤ 2*traceTwoNorm τ a^2+2*traceTwoNorm τ b^2 := by
  have h := traceTwoNorm_add_le τ a b
  have h0 := traceTwoNorm_nonneg τ (a+b)
  have h1 := traceTwoNorm_nonneg τ a
  have h2 := traceTwoNorm_nonneg τ b
  nlinarith [sq_nonneg (traceTwoNorm τ a-traceTwoNorm τ b)]

lemma energy_le (V : BistochasticTest D) (τ : TracialState D) (d : D) :
    V.energy τ d ≤ 4*traceTwoNorm τ d^2 := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    square_add_le τ (V.coeff i*d) (-(d*V.coeff i))
  simp only [← sub_eq_add_neg,traceTwoNorm_neg,Finset.sum_add_distrib,← Finset.mul_sum,
    V.sum_mul_energy τ d,V.sum_energy_mul τ d] at h
  dsimp [energy]
  linarith

lemma energy_perturb (V : BistochasticTest D) (τ : TracialState D) (t y : D) :
    V.energy τ t ≤ 2*V.energy τ y+8*traceTwoNorm τ (t-y)^2 := by
  have he (i : Fin V.size) : V.coeff i*t-t*V.coeff i =
      (V.coeff i*y-y*V.coeff i)+(V.coeff i*(t-y)-(t-y)*V.coeff i) := by noncomm_ring
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    square_add_le τ (V.coeff i*y-y*V.coeff i) (V.coeff i*(t-y)-(t-y)*V.coeff i)
  simp only [← he,Finset.sum_add_distrib,← Finset.mul_sum] at h
  change V.energy τ t ≤ 2*V.energy τ y+2*V.energy τ (t-y) at h
  linarith [V.energy_le τ (t-y)]

lemma overlap_le (V : BistochasticTest D) (τ : TracialState D) {z : D}
    (hz : IsStarProjection z) :
    (τ.functional (z*weightedAverage (fun _ : Fin V.size => (1 : ℝ)) V.coeff (1-z))).re ≤
      V.energy τ z := by
  rw [weightedAverage_overlap τ _ _ hz hz.one_sub]
  simp only [one_mul]
  apply Finset.sum_le_sum
  intro i _
  have he : z*V.coeff i*(1-z) = (z*V.coeff i-V.coeff i*z)*(1-z) := by
    noncomm_ring [hz.isIdempotentElem.eq]
  have hn : traceTwoNorm τ (z*V.coeff i*(1-z)) ≤
      traceTwoNorm τ (V.coeff i*z-z*V.coeff i) := by
    rw [he]
    apply (traceTwoNorm_mul_right τ _ _).trans
    rw [traceTwoNorm_sub_swap]
    exact (mul_le_mul_of_nonneg_right hz.one_sub.norm_le (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _)
  exact (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _)).mpr hn

end BistochasticTest

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.BlockSampling
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

section PreciseRound

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma PackingStepBounds.mono_quality {p z y t : D} {c σ η δ : ℝ}
    {K : Finset (unitary D)} (H : PackingStepBounds p z y t c σ δ K)
    (hp : IsStarProjection p) (hy : IsStarProjection y) (hc : 0 ≤ c) (hση : σ ≤ η) :
    PackingStepBounds p z y t c η δ K := by
  refine { H with sampled_linear := ?_, sampled_energy := ?_ }
  · intro x hx τ
    exact (H.sampled_linear x hx τ).trans (by
      gcongr
      exact add_nonneg (τ.functional.map_nonneg hy.nonneg).1
        (mul_nonneg hc (τ.functional.map_nonneg hp.nonneg).1))
  · intro x hx τ
    exact (H.sampled_energy x hx τ).trans (by
      gcongr
      exact add_nonneg (τ.functional.map_nonneg hy.nonneg).1
        (mul_nonneg hc (τ.functional.map_nonneg hp.nonneg).1))

lemma exists_precise_packing_round (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {z₀ r : D} (hz₀ : IsStarProjection z₀) (F : WeightedBlockFamily r)
    (K : Finset (unitary D)) {η σ δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hση : σ ≤ η) (hδ : 0 < δ)
    (happrox : ∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
      ‖F.range j*(x : D)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) :
    ∃ R : SampledPackingRound F z₀ K η δ, ∀ a,
      PackingStepBounds (F.range a.1) (R.occupied a) (R.sampled a) (R.inserted a)
        (η*F.weight a.1/2) σ δ K := by
  classical
  let e := Fintype.equivFin (F.Index × Bool)
  let Q := fun (a : Fin (Fintype.card (F.Index × Bool))) (z y t : D) =>
    PackingStepBounds (F.range (e.symm a).1) z y t (η*F.weight (e.symm a).1/2) σ δ K
  have hc (a : F.Index × Bool) : η*F.weight a.1/2 ∈ Set.Icc (0 : ℝ) 1 := by
    have hw := F.weight_le_one a.1
    have hw0 := F.weight_pos a.1
    constructor
    · positivity
    · nlinarith
  have hstep (a : Fin (Fintype.card (F.Index × Bool))) (z : D) (hz : IsStarProjection z) :
      ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1-z ∧ Q a z y t :=
    exists_packing_step (F.row (e.symm a).1) hRR hsmall hz K (hc _) (hση.trans_lt hη1) hδ (happrox _)
  obtain ⟨S,hS⟩ := exists_projection_insertion _ hz₀ Q hstep
  let R : SampledPackingRound F z₀ K η δ := {
    final := S.occupied (Fin.last _)
    occupied := fun a => S.occupied (e a).castSucc
    sampled := fun a => S.sampled (e a)
    inserted := fun a => S.inserted (e a)
    final_projection := S.occupied_projection _
    occupied_projection := fun a => S.occupied_projection _
    sampled_projection := fun a => S.sampled_projection _
    inserted_projection := fun a => S.inserted_projection _
    occupied_le_final := fun a => S.monotone (Fin.le_last _)
    inserted_orthogonal := fun a b hab => S.orthogonal (e.injective.ne hab)
    initial_orthogonal := fun a => S.initial_orthogonal _
    final_eq := by rw [e.sum_comp S.inserted]; exact S.final_eq
    bounds := by
      intro a
      have h : PackingStepBounds (F.range a.1) (S.occupied (e a).castSucc)
          (S.sampled (e a)) (S.inserted (e a)) (η*F.weight a.1/2) σ δ K := by
        simpa only [Q,Equiv.symm_apply_apply] using hS (e a)
      exact h.mono_quality (F.range_projection a.1) (S.sampled_projection _) (hc a).1 hση }
  refine ⟨R,?_⟩
  intro a
  simpa only [Q,Equiv.symm_apply_apply] using hS (e a)

namespace SampledPackingRound

variable {z₀ r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η σ δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

omit [StarOrderedRing D] in
lemma precise_sampled_energy_sum
    (H : ∀ a, PackingStepBounds (F.range a.1) (R.occupied a) (R.sampled a) (R.inserted a)
      (η*F.weight a.1/2) σ δ K) (τ : TracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, traceTwoNorm τ ((x : D)*R.sampled a-R.sampled a*(x : D))^2) ≤
      η*(∑ j, F.weight j*traceTwoNorm τ ((x : D)*F.range j-F.range j*(x : D))^2)+
        6*σ*(R.sampledMass τ+R.targetMass τ)+10*R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (H a).sampled_energy x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sampledMass,targetMass,totalError]
  rw [signed_weighted_sum F η (fun j => traceTwoNorm τ ((x : D)*F.range j-F.range j*(x : D))^2),
    signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

lemma inserted_row_energy (V : BistochasticTest D) (τ : TracialState D) :
    (∑ a, V.energy τ (R.inserted a)) ≤
      2*(∑ a, V.energy τ (R.sampled a))+40*R.overlap τ := by
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have he := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => V.energy_perturb τ (R.inserted a) (R.sampled a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hd he
  dsimp [overlap]
  linarith

end SampledPackingRound

end PreciseRound

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

variable [PartialOrder D] [StarOrderedRing D]

lemma average_le_one (V : BistochasticTest D) {r : D} (hr : IsStarProjection r) :
    weightedAverage (fun _ => (1 : ℝ)) V.coeff r ≤ 1 := by
  have h (i : Fin V.size) : V.coeff i*r*star (V.coeff i) ≤ V.coeff i*star (V.coeff i) := by
    simpa only [mul_one] using star_right_conjugate_le_conjugate hr.le_one (V.coeff i)
  simpa only [weightedAverage,one_smul,V.row] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

end BistochasticTest

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.NuclearPacking
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

section NuclearPacking

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem finite_packing_from_nuclearity
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hT : Nonempty (TracialState D))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (n : ℕ)
    (K : Finset (unitary A)) (S : Finset (BistochasticTest A)) :
    ∃ Q : OrthogonalProjectionPair D, PackingBounds ι Q K η n ∧
      ∀ W ∈ S, ∀ τ : TracialState D,
        ∑ i, Q.energy τ (ι (W.coeff i)) ≤ packingEnergy η n := by
  classical
  induction n generalizing S with
  | zero =>
    refine ⟨.zero,?_,?_⟩
    · constructor
      · intro x hx τ
        simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.energy]
      · intro τ
        simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.remaining,
          OrthogonalProjectionPair.total,τ.normalized]
      · intro x hx τ
        simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.balance]
    · intro W hW τ
      simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.energy]
  | succ n ih =>
    obtain ⟨M,σ,L,V,hM,hσ,hση,hMσ,hKL,hL,hblocks⟩ :=
      nuclear_prepared_row_blocks hA ι hRR hT K S hη hη1
    obtain ⟨Q,hQ,hQS⟩ := ih (insert V S)
    obtain ⟨F,hcomp,hclose,hblock⟩ := hblocks (1-Q.total) Q.total_projection.one_sub
    let LD := L.image (mapUnitary ι)
    let δ := η^2/(M*((Fintype.card (F.Index × Bool) : ℝ)+1))
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hcompD : ∀ j, ∀ x ∈ LD, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j*(x : D)*F.range j-(F.row j).matrix (F.base j) H‖ < σ := by
      intro j x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact hcomp j u hu
    obtain ⟨R,hRprec⟩ := exists_precise_packing_round hRR hsmall Q.total_projection F LD
      hη hη1 hση hδ hcompD
    have herror0 : 0 ≤ R.totalError := by
      dsimp [SampledPackingRound.totalError]
      positivity
    have hMerror : M*R.totalError ≤ η^2 := by
      dsimp [SampledPackingRound.totalError,δ]
      have hc : 0 ≤ (Fintype.card (F.Index × Bool) : ℝ) := by positivity
      apply (mul_le_mul_iff_right₀ (show 0 < M*((Fintype.card (F.Index × Bool) : ℝ)+1) by positivity)).mp
      field_simp
      nlinarith [sq_nonneg η]
    have herror : R.totalError ≤ η^2 :=
      (le_mul_of_one_le_left herror0 hM).trans hMerror
    have hE : 0 ≤ packingEnergy η n := packingEnergy_nonneg hη.le n
    have hold (τ : TracialState D) :
        (τ.functional (Q.total*weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff (1-Q.total))).re ≤
          4*packingEnergy η n := by
      apply ((V.map ι).overlap_le τ Q.total_projection).trans
      have ht : (V.map ι).energy τ Q.total ≤ ∑ i, Q.energy τ (ι (V.coeff i)) :=
        Finset.sum_le_sum fun i _ => Q.total_energy_le τ (ι (V.coeff i))
      exact (ht.trans (hQS V (Finset.mem_insert_self _ _) τ)).trans (by linarith)
    have hmass (τ : TracialState D) :
        (τ.functional (1-Q.total)).re-η^2 ≤
          (τ.functional (weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff (1-Q.total))).re ∧
        (τ.functional (weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff (1-Q.total))).re ≤
          (τ.functional (1-Q.total)).re := by
      rw [kraus_average_trace τ _ (V.map ι).col]
      constructor <;> nlinarith [sq_nonneg η]
    have hblockD : ∀ x ∈ LD, ∀ τ : TracialState D,
        ∑ j, F.weight j*traceTwoNorm τ ((x : D)*F.range j-F.range j*(x : D))^2 ≤ 6*σ := by
      intro x hx τ
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact hblock u hu τ
    have H : R.Estimates (packingEnergy η n) := R.estimates_of_average Q.total_projection hη hη1 hE
      (weightedAverage_nonneg (fun _ => (1 : ℝ)) (V.map ι).coeff (fun _ => zero_le_one)
        Q.total_projection.one_sub.nonneg)
      ((V.map ι).average_le_one Q.total_projection.one_sub)
      herror hmass hclose (fun x hx τ => (hblockD x hx τ).trans (by linarith)) hold
    refine ⟨Q.appendRound R,?_,?_⟩
    · constructor
      · intro x hx τ
        rw [packingEnergy_succ]
        apply (Q.appendRound_energy R τ (ι (x : A))).trans
        exact add_le_add (hQ.energy x hx τ)
          (H.inserted_energy (mapUnitary ι x) (Finset.mem_image_of_mem _ (hKL hx)) τ)
      · intro τ
        change (τ.functional (1-(Q.appendRound R).total)).re ≤ _
        rw [Q.appendRound_total R]
        apply (H.remaining τ).trans
        apply le_trans _ (packingRemainder_step hη.le n)
        apply add_le_add
        · exact add_le_add (mul_le_mul_of_nonneg_left (hQ.remaining τ) (sub_nonneg.mpr hη1.le)) le_rfl
        · exact mul_le_mul_of_nonneg_left (H.overlap_incr τ) (by norm_num)
      · intro x hx τ
        apply (Q.appendRound_balance R τ (ι (x : A))).trans
        apply le_trans _ (packingBalance_step hη.le n)
        exact add_le_add (hQ.balance x hx τ)
          (H.balance R hη herror τ (mapUnitary ι x) (Finset.mem_image_of_mem _ (hKL hx)))
    · intro W hW τ
      have hu : ∀ u ∈ L,
          ∑ a, traceTwoNorm τ (ι (u : A)*R.sampled a-R.sampled a*ι (u : A))^2 ≤
            36*σ*η+10*R.totalError := by
        intro u hu
        have hb := R.precise_sampled_energy_sum hRprec τ (mapUnitary ι u)
          (Finset.mem_image_of_mem _ hu)
        have hb' := mul_le_mul_of_nonneg_left (hblock u hu τ) hη.le
        have hc := add_le_add (H.sampled_upper τ) (H.target_upper τ)
        have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 6*σ)
        change (∑ a, traceTwoNorm τ (ι (u : A)*R.sampled a-R.sampled a*ι (u : A))^2) ≤
          η*(∑ j, F.weight j*traceTwoNorm τ (ι (u : A)*F.range j-F.range j*ι (u : A))^2)+
            6*σ*(R.sampledMass τ+R.targetMass τ)+10*R.totalError at hb
        nlinarith
      have hs := hL W hW (F.Index × Bool) R.sampled τ
        (36*σ*η+10*R.totalError) (by positivity) hu
      have hs' : ∑ a, (W.map ι).energy τ (R.sampled a) ≤ 46*η^2 := by
        have hmσ := mul_le_mul_of_nonneg_right hMσ hη.le
        nlinarith
      have hi := R.inserted_row_energy (W.map ι) τ
      have hb := H.overlap_upper τ
      have hinc : ∑ a, (W.map ι).energy τ (R.inserted a) ≤
          1000*η*(packingEnergy η n+η) := by
        nlinarith [mul_nonneg hη.le hE,sq_nonneg η]
      have hp := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
        Q.appendRound_energy R τ (ι (W.coeff i))
      rw [Finset.sum_add_distrib,Finset.sum_comm] at hp
      change (∑ i, (Q.appendRound R).energy τ (ι (W.coeff i))) ≤
        (∑ i, Q.energy τ (ι (W.coeff i)))+(∑ a, (W.map ι).energy τ (R.inserted a)) at hp
      rw [packingEnergy_succ]
      exact hp.trans (add_le_add (hQS W (Finset.mem_insert_of_mem hW) τ) hinc)

end NuclearPacking

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.FiniteSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uNuclear


section

noncomputable section

open Pureness

namespace CurrentMain

theorem finite_set_central_splitting_oai
    {A D : Type} [CStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D]
    (ι : A →⋆ₐ[ℂ] D) (_hι : Function.Injective ι)
    (hA : IsNuclear.{0, uNuclear} A) (hD : RealRankZero D)
    (hT : Nonempty (TracialState D))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    (K : Finset (unitary A)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : D, IsStarProjection P ∧ ∀ x ∈ K,
      uniformTwoNorm (P * ι (x : A) - ι (x : A) * P) < ε ∧
      uniformHalvingError P (ι (x : A)) < ε := by
  classical
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := hT
  obtain ⟨η,n,hη,hη1,henergy,hbalance⟩ := exists_packing_parameters hε
  obtain ⟨Q,hQ,_⟩ := finite_packing_from_nuclearity hA.small ι hD hT hsmall hη hη1 n K ∅
  refine ⟨Q.left,Q.left_projection,?_⟩
  intro x hx
  constructor
  · apply lt_of_le_of_lt ?_ henergy
    apply ciSup_le
    intro τ
    rw [traceTwoNorm_sub_swap]
    have h := hQ.energy x hx τ
    have hs : traceTwoNorm τ (ι (x : A)*Q.left-Q.left*ι (x : A))^2 ≤ packingEnergy η n :=
      (le_add_of_nonneg_right (sq_nonneg _)).trans h
    exact (Real.le_sqrt (traceTwoNorm_nonneg τ _) (packingEnergy_nonneg hη.le n)).mpr hs
  · apply lt_of_le_of_lt ?_ hbalance
    apply ciSup_le
    intro τ
    exact (Q.halving_le τ (mapUnitary ι x)).trans
      (div_le_div_of_nonneg_right (add_le_add (hQ.remaining τ) (hQ.balance x hx τ)) (by norm_num))

end CurrentMain

end

end

end OAI
end

theorem solution.{uNuclear} : type_of% @OAI.CurrentMain.finite_set_central_splitting_oai.{uNuclear} := @OAI.CurrentMain.finite_set_central_splitting_oai.{uNuclear}
