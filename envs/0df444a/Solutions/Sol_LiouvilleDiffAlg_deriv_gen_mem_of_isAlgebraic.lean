-- Prove2me | solution 1 for LiouvilleDiffAlg.deriv_gen_mem_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:19:47.352124+00:00
-- url     : https://prove2.me/submissions/4e495657-f4cb-41c2-a19f-e10f39ff82cd

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form

open scoped Differential
open LiouvilleDiffAlg

set_option warn.classDefReducibility false

private noncomputable def subDiff {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) : Differential K :=
  ⟨Derivation.mk'
    { toFun := fun x => ⟨(x : G)′, hK x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by simp) }
    (fun a b => Subtype.ext (by simp [Derivation.leibniz]))⟩

private lemma subDiff_coe {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) (x : K) :
    (((subDiff K hK).deriv x : K) : G) = (x : G)′ := rfl

private lemma subDiff_alg {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) :
    @DifferentialAlgebra K G _ _ _ (subDiff K hK) _ :=
  @DifferentialAlgebra.mk K G _ _ _ (subDiff K hK) _ (fun _ => rfl)

theorem solution {F G : Type*} [Field F] [Field G] [Differential G]
    [Algebra F G] [CharZero G] (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K)
    {t : G} (ht : IsAlgebraic K t) :
    t′ ∈ IntermediateField.adjoin F (insert t (K : Set G)) := by
  classical
  letI : Differential K := subDiff K hK
  haveI : DifferentialAlgebra K G := subDiff_alg K hK
  haveI : CharZero K := RingHom.charZero (algebraMap K G)
  set L := IntermediateField.adjoin F (insert t (K : Set G)) with hLdef
  have hKL : ∀ y ∈ K, y ∈ L := fun y hy =>
    IntermediateField.subset_adjoin F _ (Set.mem_insert_of_mem _ hy)
  have htL : t ∈ L := IntermediateField.subset_adjoin F _ (Set.mem_insert _ _)
  have hmem : ∀ q : Polynomial K, Polynomial.aeval t q ∈ L := by
    intro q
    rw [Polynomial.aeval_eq_sum_range]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (hKL _ (q.coeff i).2) (pow_mem htL i)
  set P := minpoly K t with hP
  have hint : IsIntegral K t := ht.isIntegral
  have hsep : P.Separable := (minpoly.irreducible hint).separable
  have hne : Polynomial.aeval t (Polynomial.derivative P) ≠ 0 :=
    hsep.aeval_derivative_ne_zero (minpoly.aeval K t)
  have hd := Differential.deriv_aeval_eq (A := K) t P
  rw [minpoly.aeval K t, map_zero] at hd
  have : t′ = -Polynomial.aeval t (Differential.mapCoeffs P) /
      Polynomial.aeval t (Polynomial.derivative P) := by
    field_simp
    linear_combination -hd
  rw [this]
  exact div_mem (neg_mem (hmem _)) (hmem _)
