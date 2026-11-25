-- Prove2me | solution 1 for GlobalTheory.exists_coboundary_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:05.3524+00:00
-- url     : https://prove2.me/submissions/fdc1d6d6-8b91-4735-a180-414324086cf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
import Theorems.Thm_GlobalTheory_exists_triple_of_card_eq_three
import Theorems.Thm_GlobalTheory_Cube_d_two_apply_triple
import Theorems.Thm_GlobalTheory_grCubeVal_add
import Theorems.Thm_GlobalTheory_grCubeVal_sub
import Theorems.Thm_GlobalTheory_grCubeVal_zero
import Theorems.Thm_GlobalTheory_grCubeVal_injective
import Theorems.Thm_GlobalTheory_grCubeVal_res
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [LinearOrder ι] [Fintype ι] {A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A)) (d : ℕ)
    (hex : Function.Exact (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 1)
      (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2))
    (N : ℕ) (F : ι → ι → MvPolynomial ι A) (hF : ∀ i j, (F i j).IsHomogeneous (d + 2 * N))
    (hcoc : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j * X l) ^ L *
      (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) :
    ∃ (N' : ℕ) (G : ι → MvPolynomial ι A), (∀ i, (G i).IsHomogeneous (d + N')) ∧
      ∀ i j, i < j → ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j) ^ L *
        ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  classical
  have hne : ∀ s : {s : Finset ι // s.card = 2}, s.1.Nonempty := fun s =>
    Finset.card_pos.1 (by rw [s.2]; norm_num)
  let x : Cube.Term (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2 := fun s =>
    ⟨awayFrac _ (xProd A s.1) N
        (Submodule.Quotient.mk (p := J) (F (s.1.min' (hne s)) (s.1.max' (hne s)))),
      awayFrac_mem_homLoc ⟨_, mem_polyGrading_natCast.2 (hF _ _), rfl⟩
        (by rw [s.2]; push_cast; ring)⟩
  have hmin : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).min' hn = i :=
    fun i j h hn => le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [h.le]))
  have hmax : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).max' hn = j :=
    fun i j h hn => le_antisymm (Finset.max'_le _ _ _ (by simp [h.le])) (Finset.le_max' _ _ (by simp))
  have hx : ∀ i j (h : i < j), grCubeVal (x ⟨{i, j}, Finset.card_pair h.ne⟩) =
      awayFrac _ (xProd A {i, j}) N (Submodule.Quotient.mk (p := J) (F i j)) := by
    intro i j h
    show awayFrac _ _ N _ = _
    rw [hmin i j h, hmax i j h]
  have hdx : Cube.d _ 2 x = 0 := by
    funext ⟨t, ht⟩
    obtain ⟨i, j, l, hij, hjl, rfl⟩ := exists_triple_of_card_eq_three ht
    rw [Cube.d_two_apply_triple _ x hij hjl]
    have hil := hij.trans hjl
    apply grCubeVal_injective
    rw [grCubeVal_add, grCubeVal_sub, grCubeVal_res, grCubeVal_res, grCubeVal_res, hx j l hjl,
      hx i l hil, hx i j hij, Pi.zero_apply, grCubeVal_zero]
    have hP : (∏ k ∈ ({i, j, l} : Finset ι), (X k : MvPolynomial ι A)) = X i * X j * X l := by
      rw [Finset.prod_insert (by simp [hij.ne, hil.ne]), Finset.prod_pair hjl.ne, mul_assoc]
    rw [locRes_awayFrac X _ (c := X i) (by rw [hP, Finset.prod_pair hjl.ne]; ring),
      locRes_awayFrac X _ (c := X j) (by rw [hP, Finset.prod_pair hil.ne]; ring),
      locRes_awayFrac X _ (c := X l) (by rw [hP, Finset.prod_pair hij.ne]; ring),
      ← map_sub, ← map_add, awayFrac_eq_zero_iff]
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hL' := Ideal.Quotient.eq_zero_iff_mem.2 hL
    rw [hP]
    simp only [map_mul, map_pow, map_add, map_sub] at hL'
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow]
    linear_combination hL'
  obtain ⟨y, hy⟩ := (hex x).1 hdx
  have hk := fun i : ι => exists_awayFrac_of_mem_homLoc (grQuot (polyGrading ι A) J)
    (Subtype.property (p := fun w => w ∈ homLoc (grQuot (polyGrading ι A) J) {i} (d : ℤ))
      (y ⟨{i}, Finset.card_singleton i⟩))
  choose k₀ hk₀ using hk
  set N' := Finset.univ.sup k₀ with hN'
  choose m hm hmeq using fun i => hk₀ i N' (Finset.le_sup (Finset.mem_univ i))
  have hmeq' : ∀ i, grCubeVal (y ⟨{i}, Finset.card_singleton i⟩) =
      awayFrac _ (xProd A {i}) N' (m i) := fun i => (hmeq i).symm
  choose g hg hgm using fun i => mem_grQuot.1 (hm i)
  refine ⟨N', fun i => -g i, fun i => ?_, fun i j h => ?_⟩
  · refine mem_polyGrading_natCast.1 ?_
    have := neg_mem (hg i)
    simp only [Finset.card_singleton] at this
    convert this using 2
    push_cast
    ring
  · have e := congrArg grCubeVal (congrFun hy ⟨{i, j}, Finset.card_pair h.ne⟩)
    rw [Cube.d_one_apply_pair _ _ h, grCubeVal_sub, grCubeVal_res, grCubeVal_res, hx i j h,
      hmeq' i, hmeq' j, ← hgm i, ← hgm j,
      locRes_awayFrac X _ (c := X i) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]),
      locRes_awayFrac X _ (c := X j) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]; ring),
      ← map_sub, awayFrac_eq_iff] at e
    obtain ⟨l, hl⟩ := e
    rw [Finset.prod_pair h.ne] at hl
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow, mul_sub] at hl
    refine ⟨l, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simp only [map_mul, map_pow, map_sub, map_neg]
    linear_combination (exp := 1) -hl
end GlobalTheory
