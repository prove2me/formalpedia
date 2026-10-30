-- Prove2me | solution 1 for OAI.TorsionFreeBass.domain_idempotent_tf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:04:17.871243+00:00
-- url     : https://prove2.me/submissions/5bf6134b-68f8-482f-b078-1e609fb63025

import Mathlib
import Definitions.Def_BassTorsionFree
import Definitions.Def_OAIQ113B001
import Theorems.Thm_OAI_TorsionFreeBass_scalar_trace_eq_augmentation_tf

section
-- module Solutions.OAIQ113_TFB.BassTrace_CoefficientDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Descent through countable coefficient rings. -/

open scoped Classical
noncomputable section
namespace TorsionFreeBass

/-- A countable characteristic-zero field admits an embedding in the complex numbers. -/
theorem countable_field_embeds_complex (F : Type*) [Field F] [CharZero F] [Countable F] :
    Nonempty (F →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hc : Cardinal.mk ℂ = Cardinal.mk t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      _ ht (by simp) (by simpa using Cardinal.aleph0_lt_continuum)
  have : Infinite t := by
    by_contra! h
    have : Finite t := h
    have hf := Cardinal.lt_aleph0_of_finite t
    rw [← hc, Cardinal.mk_complex] at hf
    exact (not_lt_of_ge Cardinal.aleph0_lt_continuum.le) hf
  let : Encodable s := Encodable.ofCountable s
  let j : s ↪ t := (Encodable.encode' s).trans (Infinite.natEmbedding t)
  let A := Algebra.adjoin ℚ (Set.range (fun x : s => (x : F)))
  let f : A →+* ℂ := (MvPolynomial.aeval (fun x : s => (j x : ℂ))).toRingHom.comp
    hs.1.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f :=
    (algebraicIndependent_iff_injective_aeval.mp (ht.1.comp j j.injective)).comp
      hs.1.aevalEquiv.symm.injective
  let : Algebra A ℂ := f.toAlgebra
  have : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : Algebra.IsAlgebraic A F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[A] ℂ).toRingHom⟩

/-- The countable coefficient ring itself embeds, without an embedding of the ambient domain. -/
theorem countable_domain_embeds_complex (R : Type*) [CommRing R] [IsDomain R]
    [CharZero R] [Countable R] : ∃ f : R →+* ℂ, Function.Injective f := by
  have : Countable (FractionRing R) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors R))
  obtain ⟨f⟩ := countable_field_embeds_complex (FractionRing R)
  exact ⟨f.comp (algebraMap R (FractionRing R)),
    f.injective.comp (IsFractionRing.injective R (FractionRing R))⟩

/-- Descent of the scalar idempotent assertion from complex coefficients to a
characteristic-zero domain, using only the finitely many coefficients. -/
theorem descend_idempotents {G : Type*} [Group G]
    (hC : ∀ e : MonoidAlgebra ℂ G, e * e = e → e = 0 ∨ e = 1)
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (e : MonoidAlgebra R G) (he : e * e = e) : e = 0 ∨ e = 1 := by
  let S := e.coeff.support
  let v : S → R := fun g => e.coeff g
  let f : MvPolynomial S ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) v
  let R₀ := f.range
  have hmem (g : G) : e.coeff g ∈ R₀ := by
    by_cases h : g ∈ S
    · exact ⟨MvPolynomial.X ⟨g,h⟩, by simp [f, v]⟩
    · have hz : e.coeff g = 0 := Finsupp.notMem_support_iff.mp h
      rw [hz]
      exact R₀.zero_mem
  have : Countable (MvPolynomial S ℤ) :=
    Function.Injective.countable AddMonoidAlgebra.coeff_injective
  have : Countable R₀ := Function.Surjective.countable f.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := countable_domain_embeds_complex R₀
  let a : MonoidAlgebra R₀ G := MonoidAlgebra.ofCoeff
    (Finsupp.onFinset S (fun g : G => (⟨e.coeff g, hmem g⟩ : R₀))
      (fun g hg => Finsupp.mem_support_iff.mpr (by simpa using hg)))
  let i : MonoidAlgebra R₀ G →+* MonoidAlgebra R G := MonoidAlgebra.mapRingHom G R₀.subtype
  have hi : Function.Injective i := MonoidAlgebra.map_injective R₀.subtype.toAddMonoidHom
    Subtype.val_injective
  have ha : i a = e := by ext g; rfl
  have ha' : a * a = a := hi (by rw [map_mul, ha, he])
  let k := MonoidAlgebra.mapRingHom G j
  have hk : Function.Injective k := MonoidAlgebra.map_injective j.toAddMonoidHom hj
  rcases hC (k a) (by rw [← map_mul, ha']) with hz | ho
  · left
    have : a = 0 := hk (hz.trans (map_zero k).symm)
    rw [← ha, this, map_zero]
  · right
    have : a = 1 := hk (ho.trans (map_one k).symm)
    rw [← ha, this, map_one]

end TorsionFreeBass
end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_RegularRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular representation on square-summable functions. -/

open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular

variable {G : Type*} [Group G]

lemma left_right_commute (g h : G) (x : Hilbert G) :
    leftShift g (rightShift h x) = rightShift h (leftShift g x) := by
  ext k
  simp [mul_assoc]

lemma convolution_apply (a : MonoidAlgebra ℂ G) (x : Hilbert G) :
    convolution a x = ∑ g ∈ a.coeff.support, a.coeff g • leftShift g x := by
  simp [convolution, MonoidAlgebra.lift_apply, Finsupp.sum]

lemma convolution_rightShift (a : MonoidAlgebra ℂ G) (g : G) (x : Hilbert G) :
    convolution a (rightShift g x) = rightShift g (convolution a x) := by
  simp only [convolution_apply, map_sum, map_smul, left_right_commute]

lemma convolution_delta (a : MonoidAlgebra ℂ G) (g : G) :
    convolution a (delta 1) g = a.coeff g := by
  simp only [convolution_apply, leftShift_delta, mul_one, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, delta_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hg
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hg).symm

omit [Group G] in
lemma inner_delta (g : G) (x : Hilbert G) : inner ℂ (delta g) x = x g := by
  simp [delta, lp.inner_single_left]

/-- Traciality against a finite convolution operator follows just from right invariance. -/
lemma trace_commute (a : MonoidAlgebra ℂ G) (T : Hilbert G →L[ℂ] Hilbert G)
    (hT : ∀ g x, T (rightShift g x) = rightShift g (T x)) :
    T (convolution a (delta 1)) 1 = convolution a (T (delta 1)) 1 := by
  simp only [convolution_apply, map_sum, map_smul, leftShift_delta, mul_one]
  have hh (g : G) : T (delta g) = rightShift g (T (delta 1)) := by
    simpa only [rightShift_delta, one_mul] using hT g (delta 1)
  change (∑ g ∈ a.coeff.support, a.coeff g • T (delta g)) 1 =
    (∑ g ∈ a.coeff.support, a.coeff g • leftShift g (T (delta 1))) 1
  have heq (g : G) : T (delta g) 1 = leftShift g (T (delta 1)) 1 := by
    rw [hh]
    simp only [rightShift_apply, leftShift_apply, one_mul, mul_one]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, heq]

end TorsionFreeBass.Regular
end


/-! Faithfulness of the coefficient trace on complex group-ring idempotents. -/

open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular

variable {G : Type*} [Group G]

/-- A right-translation-invariant closed subspace has a right-invariant orthogonal projection. -/
lemma projection_rightShift (M : Submodule ℂ (Hilbert G)) [M.HasOrthogonalProjection]
    (hM : ∀ g x, x ∈ M → rightShift g x ∈ M) (g : G) (x : Hilbert G) :
    M.starProjection (rightShift g x) = rightShift g (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (M.starProjection_apply_mem x)
  · intro w hw
    calc
      inner ℂ (rightShift g x - rightShift g (M.starProjection x)) w =
          inner ℂ (rightShift g (x - M.starProjection x))
            (rightShift g (rightShift g⁻¹ w)) := by rw [map_sub, rightShift_inv]
      _ = inner ℂ (x - M.starProjection x) (rightShift g⁻¹ w) :=
        (rightShift g).inner_map_map _ _
      _ = 0 := M.starProjection_inner_eq_zero x _ (hM _ _ hw)

/-- The coefficient trace detects zero idempotents in the complex group ring.
We project onto the closed range of left convolution. This projection has the
same coefficient trace as the idempotent, and its trace is faithful. -/
theorem idempotent_eq_zero_of_coeff_one_eq_zero (a : MonoidAlgebra ℂ G)
    (ha : a * a = a) (hzero : a.coeff 1 = 0) : a = 0 := by
  let E := convolution a
  have hEE (x : Hilbert G) : E (E x) = E x := by
    change (convolution a * convolution a) x = convolution a x
    rw [← map_mul, ha]
  let M : Submodule ℂ (Hilbert G) := (E - 1).ker
  have memM (x : Hilbert G) : x ∈ M ↔ E x = x := by
    change (E - 1) x = 0 ↔ _
    simp only [sub_apply, one_apply_eq_self, sub_eq_zero]
  have hEP (x : Hilbert G) : E (M.starProjection x) = M.starProjection x :=
    (memM _).mp (M.starProjection_apply_mem x)
  have hPE (x : Hilbert G) : M.starProjection (E x) = E x :=
    Submodule.starProjection_eq_self_iff.mpr ((memM _).mpr (hEE x))
  have hM (g : G) (x : Hilbert G) (hx : x ∈ M) : rightShift g x ∈ M := by
    apply (memM _).mpr
    change convolution a (rightShift g x) = rightShift g x
    rw [convolution_rightShift, (memM x).mp hx]
  have hPcomm := projection_rightShift M hM
  have ht : (M.starProjection (delta 1)) 1 = 0 := by
    have h := trace_commute a M.starProjection hPcomm
    change M.starProjection (E (delta 1)) 1 = E (M.starProjection (delta 1)) 1 at h
    rw [hPE, hEP] at h
    rw [← h]
    exact (convolution_delta a 1).trans hzero
  have hPδ : M.starProjection (delta 1) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [M.inner_starProjection_left_eq_right]
    rw [Submodule.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)]
    exact (inner_delta _ _).trans ht
  have hPδg (g : G) : M.starProjection (delta g) = 0 := by
    have h := hPcomm g (delta 1)
    rw [rightShift_delta, one_mul, hPδ, map_zero] at h
    exact h
  have hP (x : Hilbert G) : M.starProjection x = 0 := by
    ext g
    have h := M.inner_starProjection_left_eq_right (delta g) x
    rw [hPδg, inner_zero_left, inner_delta] at h
    exact h.symm
  have hEδ : E (delta 1) = 0 := (hPE _).symm.trans (hP _)
  ext g
  change a.coeff g = 0
  rw [← convolution_delta]
  change E (delta 1) g = 0
  rw [hEδ]
  rfl

end TorsionFreeBass.Regular
end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TorsionFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Idempotent and trace consequences for torsion-free groups. -/

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

variable {G : Type*} [Group G]

/-- Kaplansky's scalar idempotent assertion over the complex numbers. -/
theorem complex_idempotent (hG : TorsionFree G)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have ht : e.coeff 1 = augmentation e := scalar_trace_eq_augmentation_tf hG e he
  have haug : augmentation e * (augmentation e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  rcases mul_eq_zero.mp haug with hz | ho
  · exact Or.inl (Regular.idempotent_eq_zero_of_coeff_one_eq_zero e he (ht.trans hz))
  · have ht' : e.coeff 1 = 1 := ht.trans (sub_eq_zero.mp ho)
    have hc : (1 - e) * (1 - e) = 1 - e := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, he]
      abel
    have hz : (1 - e).coeff 1 = 0 := by simp [ht']
    exact Or.inr (sub_eq_zero.mp
      (Regular.idempotent_eq_zero_of_coeff_one_eq_zero (1 - e) hc hz)).symm

/-- Kaplansky's assertion over any commutative characteristic-zero domain. -/
theorem domain_idempotent_tf_oai (hG : TorsionFree G)
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (e : MonoidAlgebra R G) (he : e * e = e) : e = 0 ∨ e = 1 :=
  descend_idempotents (complex_idempotent hG) R e he

end TorsionFreeBass
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TorsionFreeBass.domain_idempotent_tf_oai.{u_1, u_2} := @OAI.TorsionFreeBass.domain_idempotent_tf_oai.{u_1, u_2}
