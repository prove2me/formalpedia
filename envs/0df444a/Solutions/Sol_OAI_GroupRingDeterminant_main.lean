-- Prove2me | solution 1 for OAI.GroupRingDeterminant.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:04:26.677306+00:00
-- url     : https://prove2.me/submissions/9204bf1e-b957-45b9-a3f0-22118c245fc0

import Mathlib
import Definitions.Def_GroupRingDeterminant
import Definitions.Def_OAIQWGRD000
import Theorems.Thm_OAI_KaplanskyCounterexample_finitelyPresented_counterexample
import Theorems.Thm_OAI_GroupRingDeterminant_projection_criterion

section
-- module Solutions.OAIQW_GroupRingDeterminant.Defects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR ud ul um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section Defect
variable {R : Type uR} [Ring R]

theorem defect_idempotent {x y : R} (h : x * y = 1) :
    (1 - y * x) * (1 - y * x) = 1 - y * x := by
  have hy : y * x * (y * x) = y * x := by
    calc
      y * x * (y * x) = y * (x * y) * x := by simp only [mul_assoc]
      _ = y * x := by rw [h, mul_one]
  calc
    (1 - y * x) * (1 - y * x) = 1 - y * x - y * x + y * x * (y * x) := by
      noncomm_ring
    _ = 1 - y * x := by rw [hy]; noncomm_ring

theorem mul_defect {x y : R} (h : x * y = 1) : x * (1 - y * x) = 0 := by
  simp only [mul_sub, mul_one, ← mul_assoc, h, one_mul, sub_self]

theorem defect_mul {x y : R} (h : x * y = 1) : (1 - y * x) * y = 0 := by
  simp only [sub_mul, one_mul, mul_assoc, h, mul_one, sub_self]

end Defect

section MatrixDefect
variable {R : Type uR} {d : Type ud} {l : Type ul} [Ring R] [Fintype d] [DecidableEq d]

theorem defect_factorization (X Y : Matrix d d R) (hXY : X * Y = 1)
    (f : Matrix l d R) (w : Matrix d l R) :
    Matrix.fromRows X (f * (1 - Y * X)) * Matrix.fromCols Y ((1 - Y * X) * w) =
      Matrix.fromBlocks 1 0 0 (f * (1 - Y * X) * w) := by
  rw [Matrix.fromRows_mul_fromCols, hXY]
  congr 1
  · rw [← Matrix.mul_assoc, mul_defect hXY, Matrix.zero_mul]
  · rw [Matrix.mul_assoc, defect_mul hXY, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc f, defect_idempotent hXY]

end MatrixDefect

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.FiniteFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uF uG ud

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section FiniteFieldPassage

variable {K : Type uK} {F : Type uF} {G : Type uG} {d : Type ud} [Semiring K] [Semiring F] [Monoid G]
variable [Fintype d] [DecidableEq d]

theorem coeffMatrix_injective (φ : K →+* Matrix d d F) (hφ : Function.Injective φ) :
    Function.Injective (coeffMatrixHom (G := G) φ) := by
  intro a b hab
  ext g
  apply hφ
  ext i j
  exact congrArg (fun A : Matrix d d (MonoidAlgebra F G) => (A i j).coeff g) hab

 theorem binary_matrix_of_finite_field (K H : Type) [Field K] [Finite K] [CharP K 2]
     [Group H] (a b : MonoidAlgebra K H) (hab : a * b = 1) (hba : b * a ≠ 1) :
     ∃ d : ℕ, 1 ≤ d ∧ ∃ X Y : Matrix (Fin d) (Fin d) (MonoidAlgebra (ZMod 2) H),
       X * Y = 1 ∧ Y * X ≠ 1 := by
   let : Algebra (ZMod 2) K := (ZMod.castHom (by simp) K).toAlgebra
   let d := Module.finrank (ZMod 2) K
   let φ : K →+* Matrix (Fin d) (Fin d) (ZMod 2) :=
     (Algebra.leftMulMatrix (Module.finBasis (ZMod 2) K)).toRingHom
   have hφ : Function.Injective φ := Algebra.leftMulMatrix_injective _
   let f : MonoidAlgebra K H →+* Matrix (Fin d) (Fin d) (MonoidAlgebra (ZMod 2) H) :=
     coeffMatrixHom φ
   refine ⟨d, Module.finrank_pos, f a, f b, ?_, ?_⟩
   · rw [← map_mul, hab, map_one]
   · intro h
     apply hba
     apply coeffMatrix_injective φ hφ
     simpa [f] using h

end FiniteFieldPassage

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.GroupAlgebraStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR uG uF uS uH

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section GroupStar
variable {R : Type uR} {G : Type uG} [Semiring R] [StarRing R] [Group G]

variable {S : Type uS} [Semiring S] [StarRing S]

variable {H : Type uH} [Group H]
lemma groupAlgebra_mapDomain_star (f : G →* H) (a : MonoidAlgebra R G) :
    MonoidAlgebra.mapDomainRingHom R f (star a) = star (MonoidAlgebra.mapDomainRingHom R f a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | single g r => simp

end GroupStar

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.CyclicAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace AverageDraft
section Algebra
variable {A : Type uA} [Ring A] [Algebra ℚ A]
lemma thirdAverage_square (z : A) (hz : z * z * z = 1) :
    thirdAverage z * thirdAverage z = thirdAverage z := by
  have hz4 : z * z * (z * z) = z := by rw [← mul_assoc, hz, one_mul]
  have he : (1 + z + z * z) * (1 + z + z * z) =
      (3 : ℚ) • (1 + z + z * z) := by
    calc
      _ = 1 + z + z + z * z + z * z + z * z +
          z * z * z + z * z * z + z * z * (z * z) := by noncomm_ring
      _ = _ := by rw [hz, hz4]; simp only [show (3 : ℚ) = 1 + 1 + 1 by norm_num,
        add_smul, one_smul]; abel
  simp only [thirdAverage, smul_mul_smul_comm, he, smul_smul]
  norm_num

end Algebra
end AverageDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ProductSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uB uC uI

noncomputable section
open scoped BigOperators Pointwise

namespace SupportDraft
variable {B : Type uB} {C : Type uC} {I : Type uI} [CommGroup B] [Group C]
variable (coord : I → B →* C)

lemma supportedOn_single (s : Set I) (b : B) (q : ℚ)
    (hb : ∀ i, i ∉ s → coord i b = 1) : SupportedOn coord s (MonoidAlgebra.single b q) := by
  classical
  intro g hg i hi
  by_cases hgb : g = b
  · subst g; exact hb i hi
  · simp [MonoidAlgebra.coeff_single, Ne.symm hgb] at hg

lemma supportedOn_one (s : Set I) : SupportedOn coord s (1 : MonoidAlgebra ℚ B) := by
  rw [MonoidAlgebra.one_def]
  exact supportedOn_single coord s 1 1 (by simp)

lemma supportedOn_add {s : Set I} {a b : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hb : SupportedOn coord s b) : SupportedOn coord s (a + b) := by
  intro g hg i hi
  by_cases hga : a.coeff g = 0
  · apply hb g _ i hi
    simpa [hga] using hg
  · exact ha g hga i hi

lemma supportedOn_neg {s : Set I} {a : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) : SupportedOn coord s (-a) := by
  intro g hg i hi
  exact ha g (by simpa using hg) i hi

lemma supportedOn_sub {s : Set I} {a b : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hb : SupportedOn coord s b) : SupportedOn coord s (a - b) := by
  rw [sub_eq_add_neg]
  exact supportedOn_add coord ha (supportedOn_neg coord hb)

lemma supportedOn_smul {s : Set I} {a : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (q : ℚ) : SupportedOn coord s (q • a) := by
  intro g hg i hi
  apply ha g _ i hi
  intro h
  apply hg
  simp [h]

lemma supportedOn_mul {s t : Set I} {a b : MonoidAlgebra ℚ B}
    (ha : SupportedOn coord s a) (hb : SupportedOn coord t b) :
    SupportedOn coord (s ∪ t) (a * b) := by
  classical
  intro g hg i hi
  have hm := MonoidAlgebra.support_coeff_mul_subset a b (Finsupp.mem_support_iff.mpr hg)
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hm
  rw [map_mul, ha x (Finsupp.mem_support_iff.mp hx) i (fun h => hi (Or.inl h)),
    hb y (Finsupp.mem_support_iff.mp hy) i (fun h => hi (Or.inr h)), one_mul]

lemma coeff_one_mul_of_disjoint (hinj : ∀ b : B, (∀ i, coord i b = 1) → b = 1)
    {s t : Set I} (hst : Disjoint s t) (a b : MonoidAlgebra ℚ B)
    (ha : SupportedOn coord s a) (hb : SupportedOn coord t b) :
    (a * b).coeff 1 = a.coeff 1 * b.coeff 1 := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left]
  simp only [mul_one]
  rw [a.coeff.sum_eq_single 1]
  · simp
  · intro g hg hgne
    by_cases hbg : b.coeff g⁻¹ = 0
    · simp [hbg]
    · exfalso
      apply hgne
      apply hinj
      intro i
      by_cases his : i ∈ s
      · have hit : i ∉ t := fun h => Set.disjoint_left.mp hst his h
        have hh := hb g⁻¹ hbg i hit
        simpa using hh
      · exact ha g hg i his
  · intro _
    simp

lemma supportedOn_prod (s : Finset I) (a : I → MonoidAlgebra ℚ B)
    (ha : ∀ i ∈ s, SupportedOn coord {i} (a i)) : SupportedOn coord (s : Set I) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supportedOn_one coord ∅
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    simpa using supportedOn_mul coord (ha i (by simp)) (ih (by aesop))

lemma coeff_one_prod (hinj : ∀ b : B, (∀ i, coord i b = 1) → b = 1)
    (s : Finset I) (a : I → MonoidAlgebra ℚ B)
    (ha : ∀ i ∈ s, SupportedOn coord {i} (a i)) :
    (∏ i ∈ s, a i).coeff 1 = ∏ i ∈ s, (a i).coeff 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      coeff_one_mul_of_disjoint coord hinj (by simpa using hi) _ _ (ha i (by simp))
        (supportedOn_prod coord s a (by aesop)), ih (by aesop)]

end SupportDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.Lamps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampDraft
variable (H : Type uH) [Group H]

attribute [local instance] OAI.LampDraft.instDecidableEq_solutions
theorem lamp_cube (h : H) : lamp H h ^ 3 = 1 := by
  classical
  apply Subtype.ext
  simp only [Subgroup.coe_pow, lamp_coe, Subgroup.coe_one]
  simp only [pow_succ, pow_zero, one_mul]
  ext t
  · by_cases ht : t = h
    · subst t
      norm_num [coordinate]
      decide
    · simp [coordinate, ht]
  · simp [coordinate]

theorem shift_conjugate_lamp (s h : H) :
    shift H s * lamp H h * (shift H s)⁻¹ = lamp H (s * h) := by
  simp only [lamp, map_mul, mul_inv_rev]
  group

lemma baseCoordinate_injective {a b : BaseGroup H}
    (h : ∀ t, baseCoordinate H t a = baseCoordinate H t b) : a = b := by
  apply Subtype.ext
  apply Subtype.ext
  apply RegularWreathProduct.ext
  · exact funext h
  · exact a.property.trans b.property.symm

lemma baseLamp_cube (h : H) : baseLamp H h ^ 3 = 1 := by
  apply Subtype.ext
  exact lamp_cube H h

lemma baseLamp_ne_one (h : H) : baseLamp H h ≠ 1 := by
  intro he
  have he' := congrArg (baseCoordinate H h) he
  norm_num at he'

lemma baseLamp_sq_ne_one (h : H) : baseLamp H h * baseLamp H h ≠ 1 := by
  intro he
  have he' := congrArg (baseCoordinate H h) he
  norm_num at he'
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd 1 ≠ 1) he'

end LampDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LampProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft AverageDraft SupportDraft GroupRingDeterminant
variable (H : Type uH) [Group H]

attribute [local instance] OAI.LampProjectionDraft.instDecidableEq_solutions
lemma baseAverage_idempotent (h : H) : IsIdempotentElem (baseAverage H h) := by
  apply thirdAverage_square
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  have he : baseLamp H h * baseLamp H h * baseLamp H h = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using baseLamp_cube H h
  rw [he, ← MonoidAlgebra.one_def]

lemma baseAverage_selfAdjoint (h : H) : IsSelfAdjoint (baseAverage H h) := by
  have he : (baseLamp H h)⁻¹ = baseLamp H h * baseLamp H h :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_succ, pow_zero, one_mul, mul_assoc]
      using (baseLamp_cube H h))
  have he2 : (baseLamp H h * baseLamp H h)⁻¹ = baseLamp H h := by
    rw [← he, inv_inv]
  change star (baseAverage H h) = baseAverage H h
  simp only [baseAverage, thirdAverage, MonoidAlgebra.single_mul_single, one_mul,
    star_smul, star_add, star_one, star_groupAlgebra_single, he, he2, star_trivial]
  congr 1
  abel

lemma baseAverage_supported (h : H) : SupportedOn (baseCoordinate H) {h} (baseAverage H h) := by
  have hs : SupportedOn (baseCoordinate H) {h}
      (MonoidAlgebra.single (baseLamp H h) (1 : ℚ)) :=
    supportedOn_single _ _ _ _ (by intro i hi; simp_all)
  unfold baseAverage thirdAverage
  apply supportedOn_smul
  apply supportedOn_add
  · exact supportedOn_add _ (supportedOn_one _ _) hs
  · simpa only [Set.union_self] using supportedOn_mul _ hs hs

lemma baseAverage_trace (h : H) : (baseAverage H h).coeff 1 = 1 / 3 := by
  simp [baseAverage, thirdAverage, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.coeff_single, baseLamp_ne_one, baseLamp_sq_ne_one]

lemma complement_prod_idempotent (S : Finset H) :
    IsIdempotentElem (∏ s ∈ S, (1 - baseAverage H s)) := by
  induction S using Finset.induction_on with
  | empty => simp [IsIdempotentElem]
  | @insert s S hs ih =>
    rw [Finset.prod_insert hs]
    exact (baseAverage_idempotent H s).one_sub.mul ih

lemma baseProjection_idempotent (S : Finset H) : IsIdempotentElem (baseProjection H S) :=
  (baseAverage_idempotent H 1).mul (complement_prod_idempotent H S)

lemma complement_prod_selfAdjoint (S : Finset H) :
    IsSelfAdjoint (∏ s ∈ S, (1 - baseAverage H s)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert s S hs ih =>
    rw [Finset.prod_insert hs]
    exact ((IsSelfAdjoint.one _).sub (baseAverage_selfAdjoint H s)).mul ih

lemma baseProjection_selfAdjoint (S : Finset H) : IsSelfAdjoint (baseProjection H S) :=
  (baseAverage_selfAdjoint H 1).mul (complement_prod_selfAdjoint H S)

lemma baseProjection_trace (S : Finset H) (hS : 1 ∉ S) :
    (baseProjection H S).coeff 1 = (1 / 3 : ℚ) * (2 / 3 : ℚ) ^ S.card := by
  have hi (b : BaseGroup H) (hb : ∀ i, baseCoordinate H i b = 1) : b = 1 :=
    baseCoordinate_injective H (by simpa using hb)
  have hc (s : H) : SupportedOn (baseCoordinate H) {s} (1 - baseAverage H s) :=
    supportedOn_sub _ (supportedOn_one _ _) (baseAverage_supported H s)
  rw [baseProjection, coeff_one_mul_of_disjoint (baseCoordinate H) hi (by simpa using hS)
    _ _ (baseAverage_supported H 1) (supportedOn_prod _ _ _ (by intro i _; exact hc i)),
    baseAverage_trace, coeff_one_prod (baseCoordinate H) hi _ _ (by intro i _; exact hc i)]
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, baseAverage_trace]
  norm_num [div_pow]

end LampProjectionDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LampCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH uR

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft AverageDraft SupportDraft GroupRingDeterminant
variable (H : Type uH) [Group H]

attribute [local instance] OAI.LampProjectionDraft.instDecidableEq_solutions_1
variable (R : Type uR) [CommRing R]

variable {R}

lemma shiftSymbol_one_lamp (s : H) :
    shiftSymbol H s * fullLampSymbol H (R := R) 1 = fullLampSymbol H s * shiftSymbol H s := by
  simp only [shiftSymbol, fullLampSymbol, MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  have he := shift_conjugate_lamp H s 1
  simpa using (mul_inv_eq_iff_eq_mul.mp (by simpa using he))

lemma average_def (h : H) : average H h = thirdAverage (fullLampSymbol H h) := by
  unfold average baseAverage thirdAverage
  change _ = (1 / 3 : ℚ) • (1 + _ + _)
  rw [show (baseEmbedding H ℚ) ((1 / 3 : ℚ) • _) = (1 / 3 : ℚ) •
    (baseEmbedding H ℚ) _ from map_rat_smul _ _ _]
  simp only [map_add, map_one, map_mul]
  simp [baseEmbedding, fullLampSymbol, baseLamp]

lemma projection_idempotent (S : Finset H) : IsIdempotentElem (projection H S) :=
  (baseProjection_idempotent H S).map (baseEmbedding H ℚ)

lemma projection_selfAdjoint (S : Finset H) : IsSelfAdjoint (projection H S) := by
  change star (baseEmbedding H ℚ _) = _
  change star (MonoidAlgebra.mapDomainRingHom ℚ _ _) = _
  rw [← groupAlgebra_mapDomain_star]
  exact congrArg (baseEmbedding H ℚ) (baseProjection_selfAdjoint H S)

lemma projection_trace (S : Finset H) (hS : 1 ∉ S) :
    (projection H S).coeff 1 = (1 / 3 : ℚ) * (2 / 3 : ℚ) ^ S.card := by
  rw [projection, baseEmbedding_coeff_one, baseProjection_trace H S hS]

lemma baseAverage_one_mul_projection (S : Finset H) :
    baseAverage H 1 * baseProjection H S = baseProjection H S := by
  rw [baseProjection, ← mul_assoc, baseAverage_idempotent H 1]

lemma baseProjection_mul_average_eq_zero (S : Finset H) {s : H} (hs : s ∈ S) :
    baseProjection H S * baseAverage H s = 0 := by
  have he := Finset.mul_prod_erase S (fun t => 1 - baseAverage H t) hs
  rw [baseProjection, ← he]
  have hp := baseAverage_idempotent H s
  change _ * _ = _ at hp
  calc
    _ = baseAverage H 1 * (∏ t ∈ S.erase s, (1 - baseAverage H t)) *
          ((1 - baseAverage H s) * baseAverage H s) := by ring
    _ = 0 := by rw [sub_mul, one_mul, hp, sub_self, mul_zero]

lemma shift_average (s : H) : shiftSymbol H s * average H 1 = average H s * shiftSymbol H s := by
  have hs := shiftSymbol_one_lamp H (R := ℚ) s
  rw [average_def, average_def]
  unfold thirdAverage
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [hs]
  congr 1
  rw [← mul_assoc, hs, mul_assoc, hs, ← mul_assoc]

lemma projection_separates (S : Finset H) {s : H} (hs : s ∈ S) :
    projection H S * shiftSymbol H s * projection H S = 0 := by
  have h1 : average H 1 * projection H S = projection H S := by
    simpa only [average, projection, ← map_mul] using
      congrArg (baseEmbedding H ℚ) (baseAverage_one_mul_projection H S)
  have h0 : projection H S * average H s = 0 := by
    simpa only [average, projection, ← map_mul, map_zero] using
      congrArg (baseEmbedding H ℚ) (baseProjection_mul_average_eq_zero H S hs)
  calc
    _ = projection H S * shiftSymbol H s * (average H 1 * projection H S) := by rw [h1]
    _ = projection H S * (shiftSymbol H s * average H 1) * projection H S := by simp only [mul_assoc]
    _ = projection H S * (average H s * shiftSymbol H s) * projection H S := by rw [shift_average]
    _ = 0 := by rw [← mul_assoc, h0, zero_mul, zero_mul]

lemma intToRat_baseSum (h : H) : intToRat H (baseSum H h) = (3 : ℚ) • baseAverage H h := by
  simp [intToRat, baseSum, baseAverage, thirdAverage, smul_smul, pow_two]

lemma intToRat_baseNumerator (S : Finset H) :
    intToRat H (baseNumerator H S) = (denominator H S : ℚ) • baseProjection H S := by
  have he (s : H) : intToRat H (3 - baseSum H s) = (3 : ℚ) • (1 - baseAverage H s) := by
    rw [map_sub, map_ofNat, intToRat_baseSum, smul_sub]
    simp only [← Algebra.algebraMap_eq_smul_one, map_ofNat]
  simp only [baseNumerator, map_mul, map_prod, intToRat_baseSum, he]
  rw [Finset.prod_smul, Finset.prod_const, smul_mul_smul_comm]
  simp [denominator, baseProjection, pow_succ, mul_comm]

omit [Group H] in
lemma denominator_odd (S : Finset H) : Odd (denominator H S) := by
  exact (by decide : Odd 3).pow

end LampProjectionDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LampDenominators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft GroupRingDeterminant
variable (H : Type uH) [Group H]

local instance instDecidableEq_solutions_2_rfea081_1 : DecidableEq H := Classical.decEq H
lemma fullIntToRat_injective : Function.Injective (fullIntToRat H) :=
  MonoidAlgebra.map_injective (Int.castRingHom ℚ).toAddMonoidHom Int.cast_injective

lemma fullIntToRat_baseEmbedding (a : MonoidAlgebra ℤ (BaseGroup H)) :
    fullIntToRat H (baseEmbedding H ℤ a) = baseEmbedding H ℚ (intToRat H a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g z => simp [fullIntToRat, intToRat, baseEmbedding]

lemma numerator_toRat (S : Finset H) :
    fullIntToRat H (numerator H S) = (denominator H S : ℚ) • projection H S := by
  rw [numerator, fullIntToRat_baseEmbedding, intToRat_baseNumerator, map_rat_smul]
  rfl

lemma fullIntToRat_zsmul (a : MonoidAlgebra ℤ (LampGroup H)) (D : ℤ) :
    fullIntToRat H (D • a) = (D : ℚ) • fullIntToRat H a := by
  rw [Int.cast_smul_eq_zsmul]
  exact map_zsmul _ _ _

lemma fullIntToBin_zsmul (a : MonoidAlgebra ℤ (LampGroup H)) (D : ℤ) :
    fullIntToBin H (D • a) = (D : ZMod 2) • fullIntToBin H a := by
  rw [Int.cast_smul_eq_zsmul]
  exact map_zsmul _ _ _

lemma numerator_square (S : Finset H) :
    numerator H S * numerator H S = (denominator H S : ℤ) • numerator H S := by
  apply fullIntToRat_injective H
  rw [map_mul, fullIntToRat_zsmul, numerator_toRat, smul_mul_smul_comm,
    projection_idempotent, smul_smul]
  simp

lemma numerator_separates (S : Finset H) {s : H} (hs : s ∈ S) :
    numerator H S * shiftSymbol H s * numerator H S = 0 := by
  apply fullIntToRat_injective H
  rw [map_mul, map_mul, map_zero, numerator_toRat]
  have hs' : fullIntToRat H (shiftSymbol H s) = shiftSymbol H s := by
    simp [fullIntToRat, shiftSymbol]
  rw [hs', smul_mul_assoc, smul_mul_smul_comm, projection_separates H S hs, smul_zero]

lemma binaryProjection_idempotent (S : Finset H) :
    IsIdempotentElem (binaryProjection H S) := by
  change fullIntToBin H _ * fullIntToBin H _ = fullIntToBin H _
  rw [← map_mul, numerator_square, fullIntToBin_zsmul, Int.cast_natCast,
    (denominator_odd H S).natCast_zmod_two, one_smul]

lemma binaryProjection_separates (S : Finset H) {s : H} (hs : s ∈ S) :
    binaryProjection H S * shiftSymbol H s * binaryProjection H S = 0 := by
  have he := congrArg (fullIntToBin H) (numerator_separates H S hs)
  simpa [binaryProjection, fullIntToBin, shiftSymbol] using he

end LampProjectionDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.BinaryMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
variable {H : Type uH} [Group H]

lemma zmodTwo_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  exact (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) z hz

lemma binary_support_expansion (a : MonoidAlgebra (ZMod 2) H) (ha : a.coeff 1 = 1) :
    ∃ S : Finset H, 1 ∉ S ∧ a = 1 + ∑ s ∈ S, MonoidAlgebra.single s 1 := by
  classical
  have hm : 1 ∈ a.coeff.support := Finsupp.mem_support_iff.mpr (ha ▸ one_ne_zero)
  refine ⟨a.coeff.support.erase 1, Finset.notMem_erase _ _, ?_⟩
  calc
    a = ∑ s ∈ a.coeff.support, MonoidAlgebra.single s (a.coeff s) :=
      (MonoidAlgebra.sum_coeff_single a).symm
    _ = MonoidAlgebra.single 1 (a.coeff 1) +
        ∑ s ∈ a.coeff.support.erase 1, MonoidAlgebra.single s (a.coeff s) :=
      (Finset.add_sum_erase _ _ hm).symm
    _ = _ := by
      rw [ha, ← MonoidAlgebra.one_def]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [zmodTwo_eq_one_of_ne_zero (a.coeff s)
        (Finsupp.mem_support_iff.mp (Finset.mem_of_mem_erase hs))]

lemma binary_coefficient_normalize (a : MonoidAlgebra (ZMod 2) H) (ha : a ≠ 0) :
    ∃ h : H, ∃ S : Finset H, 1 ∉ S ∧
      MonoidAlgebra.single h⁻¹ 1 * a = 1 + ∑ s ∈ S, MonoidAlgebra.single s 1 := by
  classical
  obtain ⟨h, hh⟩ : ∃ h, a.coeff h ≠ 0 := by
    by_contra! hn
    apply ha
    ext h
    exact hn h
  have he : (MonoidAlgebra.single h⁻¹ 1 * a).coeff 1 = 1 := by
    rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff h (by simp [inv_mul_eq_one, eq_comm])]
    exact one_mul _ |>.trans (zmodTwo_eq_one_of_ne_zero _ hh)
  obtain ⟨S, hS, he⟩ := binary_support_expansion _ he
  exact ⟨h, S, hS, he⟩
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.DefectProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
open LampDraft LampProjectionDraft
variable {H : Type} [Group H]

lemma binaryProjection_isolates {a : MonoidAlgebra (ZMod 2) H} {h : H} {S : Finset H}
    (he : MonoidAlgebra.single h⁻¹ 1 * a = 1 + ∑ s ∈ S, MonoidAlgebra.single s 1) :
    binaryProjection H S * LampProjectionDraft.shiftSymbol H h⁻¹ *
      lampRingEmbedding (ZMod 2) a * binaryProjection H S = binaryProjection H S := by
  have hmap := congrArg (lampRingEmbedding (H := H) (ZMod 2)) he
  simp only [map_mul, map_add, map_one, map_sum] at hmap
  have hn : LampProjectionDraft.shiftSymbol H h⁻¹ * lampRingEmbedding (ZMod 2) a =
      1 + ∑ s ∈ S, LampProjectionDraft.shiftSymbol H s := by
    simpa [lampRingEmbedding, LampProjectionDraft.shiftSymbol] using hmap
  rw [mul_assoc (binaryProjection H S), hn, mul_add, mul_one, add_mul,
    (binaryProjection_idempotent H S).eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_zero (fun s hs => binaryProjection_separates H S hs), add_zero]

lemma binary_defect_factorization_lamp {d : Type} [Fintype d] [DecidableEq d]
    (X Y : Matrix d d (MonoidAlgebra (ZMod 2) H)) (hXY : X * Y = 1) (hYX : Y * X ≠ 1) :
    ∃ S : Finset H, 1 ∉ S ∧
      ∃ u : Matrix (d ⊕ Unit) d (MonoidAlgebra (ZMod 2) (LampGroup H)),
      ∃ v : Matrix d (d ⊕ Unit) (MonoidAlgebra (ZMod 2) (LampGroup H)),
        u * v = Matrix.fromBlocks 1 0 0 (fun _ _ : Unit => binaryProjection H S) := by
  classical
  let C := 1 - Y * X
  have hC : C ≠ 0 := sub_ne_zero.mpr (Ne.symm hYX)
  obtain ⟨i, j, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra! he
    exact hC (Matrix.ext fun i j => he i j)
  obtain ⟨h, S, hS, he⟩ := binary_coefficient_normalize (C i j) hij
  let φ := lampRingEmbedding (H := H) (ZMod 2)
  let Xm := X.map φ
  let Ym := Y.map φ
  let Cm := C.map φ
  let p := binaryProjection H S
  let f : Matrix Unit d (MonoidAlgebra (ZMod 2) (LampGroup H)) :=
    Matrix.single () i (p * LampProjectionDraft.shiftSymbol H h⁻¹)
  let w : Matrix d Unit (MonoidAlgebra (ZMod 2) (LampGroup H)) := Matrix.single j () p
  have hXYm : Xm * Ym = 1 := by
    change X.map φ * Y.map φ = 1
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  have hCm : Cm = 1 - Ym * Xm := by
    dsimp [Cm, C, Ym, Xm]
    rw [Matrix.map_sub _ (map_sub _) _ _, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]
  have hfcw : f * Cm * w = fun _ _ : Unit => p := by
    apply Matrix.ext
    intro a b
    cases a; cases b
    dsimp only [f, w]
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same]
    exact binaryProjection_isolates he
  refine ⟨S, hS, Matrix.fromRows Xm (f * Cm), Matrix.fromCols Ym (Cm * w), ?_⟩
  rw [hCm, defect_factorization Xm Ym hXYm f w, ← hCm, hfcw]

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ProjectionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
open LampDraft LampProjectionDraft
variable {H d : Type} [Group H] [Fintype d] [DecidableEq d]

lemma lamp_projection_data (X Y : Matrix d d (MonoidAlgebra (ZMod 2) H))
    (hXY : X * Y = 1) (hYX : Y * X ≠ 1) :
    ∃ (D : ℕ), Odd D ∧ ∃ P : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℚ (LampGroup H)),
      P * P = P ∧ IsSelfAdjoint P ∧ (Fintype.card d : ℚ) < ∑ i, (P i i).coeff 1 ∧
      ∃ Z : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℤ (LampGroup H)),
        Z.map toRat = (D : ℚ) • P ∧
        ∃ u : Matrix (d ⊕ Unit) d (MonoidAlgebra (ZMod 2) (LampGroup H)),
        ∃ v : Matrix d (d ⊕ Unit) (MonoidAlgebra (ZMod 2) (LampGroup H)),
          u * v = Z.map (toMod 2) := by
  classical
  obtain ⟨S, hS, u, v, huv⟩ := binary_defect_factorization_lamp X Y hXY hYX
  let p := projection H S
  let D := denominator H S
  let P : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℚ (LampGroup H)) :=
    Matrix.fromBlocks 1 0 0 (Matrix.diagonal (fun _ : Unit => p))
  let Z : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℤ (LampGroup H)) :=
    Matrix.fromBlocks ((D : ℤ) • 1) 0 0 (Matrix.diagonal (fun _ : Unit => numerator H S))
  have hp : p * p = p := (projection_idempotent H S).eq
  have hps : star p = p := (projection_selfAdjoint H S).star_eq
  refine ⟨D, denominator_odd H S, P, ?_, ?_, ?_, Z, ?_, u, v, ?_⟩
  · dsimp only [P]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.diagonal_mul_diagonal, hp]
  · change Matrix.conjTranspose P = P
    dsimp only [P]
    rw [Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.diagonal_conjTranspose]
    congr 2
    funext i
    exact hps
  · have he : (∑ i, (P i i).coeff 1) = (Fintype.card d : ℚ) + (p.coeff 1) := by
      simp [P, Fintype.sum_sum_type]
    rw [he, lt_add_iff_pos_right]
    rw [show p = projection H S from rfl, projection_trace H S hS]
    positivity
  · apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change fullIntToRat H (((D : ℤ) • (1 : Matrix d d _)) i j) =
        (D : ℚ) • (1 : Matrix d d _) i j
      rw [show (((D : ℤ) • (1 : Matrix d d _)) i j) = (D : ℤ) • ((1 : Matrix d d _) i j) from rfl,
        fullIntToRat_zsmul]
      simp [Matrix.one_apply]
    · simp [Z, P, Matrix.map_apply]
    · simp [Z, P, Matrix.map_apply]
    · cases i; cases j
      exact numerator_toRat H S
  · rw [huv]
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change (1 : Matrix d d _) i j = fullIntToBin H (((D : ℤ) • (1 : Matrix d d _)) i j)
      rw [show (((D : ℤ) • (1 : Matrix d d _)) i j) = (D : ℤ) • ((1 : Matrix d d _) i j) from rfl,
        fullIntToBin_zsmul]
      simp [Matrix.one_apply, (denominator_odd H S).natCast_zmod_two, D]
    · simp [Z, Matrix.map_apply, Matrix.fromBlocks]
    · simp [Z, Matrix.map_apply, Matrix.fromBlocks]
    · cases i; cases j
      rfl

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.CompanionTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant

theorem main_of_companion_input (input : CompanionInput) : MainStatement := by
  obtain ⟨K, hK, hKfinite, hKchar, H, hH, hHfg, a, b, hab, hba⟩ := input
  let := hK
  let := hKfinite
  let := hKchar
  let := hH
  let := hHfg
  obtain ⟨d, hd, X, Y, hXY, hYX⟩ := binary_matrix_of_finite_field K H a b hab hba
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨D, hD, P, hP, hPs, ht, Z, hZ, u, v, huv⟩ := lamp_projection_data X Y hXY hYX
  exact projection_criterion D hD P ⟨hP, hPs⟩ ht Z hZ u v huv

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GroupRingDeterminant

theorem companion_input : CompanionInput := by
  obtain ⟨K, hK, hKfin, hKchar, H, hH, hHfp, -, a, b, hab, hba⟩ :=
    KaplanskyCounterexample.finitelyPresented_counterexample
  have hHfg : Group.FG H := by
    obtain ⟨n, φ, hφ, -⟩ := hHfp.out
    exact Group.fg_of_surjective hφ
  exact ⟨K, hK, Fintype.finite hKfin, hKchar, H, hH, hHfg, a, b, hab, hba⟩

theorem main_oai : MainStatement := main_of_companion_input companion_input

end GroupRingDeterminant

end OAI
end

theorem solution : type_of% @OAI.GroupRingDeterminant.main_oai := @OAI.GroupRingDeterminant.main_oai
