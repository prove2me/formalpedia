-- Prove2me | solution 1 for OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:20:37.644586+00:00
-- url     : https://prove2.me/submissions/9a79ba23-8336-4962-ac5f-7a4fa1cdedcd

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K024
import Theorems.Thm_OAI_KLInvariance_TitsSpace_bottCharacter_decomposition_both
import Theorems.Thm_OAI_KLInvariance_TitsSpace_bottKernelCharacter_rConvolution

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedModules
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.ModuleData.unit_free _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded polynomial modules, projective presentations, finite homogeneous generators and uniqueness of minimal covers.
-/


section

namespace KLInvariance.Graded
universe uk ua um

attribute [instance] ModuleData.kModule ModuleData.tower ModuleData.decomposition
  ModuleData.graded ModuleData.finite

end KLInvariance.Graded

end


section

/-! Homogeneous projectivity and uniqueness of the actual minimal graded
covers. These are recognition dependencies, not assumptions of the main. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

variable [IsDomain A] [IsNoetherianRing A]
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)

include hneg hzero in
 theorem MinimalCover.equiv {M : ModuleData.{uk,ua,um} 𝓐} (C D : MinimalCover M) :
    ∃ e : C.source ≃ₗ[A] D.source,
      (∀ n v, v ∈ C.source.piece n → e v ∈ D.source.piece n) ∧
      D.hom.map.comp e.toLinearMap = C.hom.map := by
  let := C.free
  let := D.free
  obtain ⟨f,hf⟩ := exists_hom_lift hneg hzero D.hom D.surjective C.hom
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective D.hom
  have hfa (v : C.source) : D.hom.map (f.map v)=C.hom.map v := LinearMap.congr_fun hf v
  have hga (v : D.source) : C.hom.map (g.map v)=D.hom.map v := LinearMap.congr_fun hg v
  have hgc : Function.Bijective (g.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply C.minimal
    change C.hom.map (m-g.map (f.map m))=0
    rw [map_sub,hga,hfa,sub_self]
  have hfd : Function.Bijective (f.comp g).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply D.minimal
    change D.hom.map (m-f.map (g.map m))=0
    rw [map_sub,hfa,hga,sub_self]
  have hfb : Function.Bijective f.map :=
    ⟨Function.Injective.of_comp hgc.1,Function.Surjective.of_comp hfd.2⟩
  exact ⟨LinearEquiv.ofBijective f.map hfb,f.graded,hf⟩

end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Bruhat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Strong Bruhat order, subwords, length, finite lower ideals and arbitrary finite intervals; the selected R family.
-/

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-- The exact R recursion determines at most one R family. -/
theorem normalized_R_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.1 = SQ.1 := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x, RP.1 x y = SQ.1 x y by
    funext x y
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        rw [hRP.R_diagonal, hSQ.R_diagonal]
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [hRP.R_zero _ _ hn, hSQ.R_zero _ _ hn]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [hRP.R_recursion x y i hi, hSQ.R_recursion x y i hi]
      rw [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

/-- The degree/reciprocity rigidity used both by normalization uniqueness and
by the final main-theorem induction: no polynomial supported strictly below
the midpoint can be self-reciprocal about that midpoint. -/
theorem low_degree_reflect_eq_self (f : ℤ[X]) (d : ℕ)
    (hd : 2 * f.natDegree < d) (hself : reflect d f = f) : f = 0 := by
  by_contra hn
  have hc := congrArg (fun p : ℤ[X] => p.coeff f.natDegree) hself
  rw [coeff_reflect, revAt_le (by omega)] at hc
  rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hn) hc.symm

/-- The polynomial part of the manuscript's normalization is unique; the
proof uses the actual finite strong-Bruhat intervals, not extra assumptions. -/
theorem normalized_P_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.2 = SQ.2 := by
  classical
  have hR := normalized_R_unique cs hRP hSQ
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → RP.2 x y = SQ.2 x y by
    funext x y
    exact this (rankDifference cs x y) x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hxy
    by_cases hcomp : BruhatLE cs x y
    · by_cases heq : x = y
      · subst y
        rw [hRP.P_diagonal, hSQ.P_diagonal]
      · let : Finite (Interval cs x y) := interval_finite cs x y
        let : Fintype (Interval cs x y) := Fintype.ofFinite _
        let bottom : Interval cs x y := ⟨x, bruhat_refl cs x, hcomp⟩
        have hsum : (∑ z : Interval cs x y,
            RP.1 x z.val * (RP.2 z.val y - SQ.2 z.val y)) = RP.2 x y - SQ.2 x y := by
          rw [Finset.sum_eq_single bottom]
          · simp [bottom, hRP.R_diagonal]
          · intro z _ hz
            have hxz : x ≠ z.val := by
              intro hc
              apply hz
              exact Subtype.ext hc.symm
            have hlt := length_lt_of_bruhat_ne cs z.property.1 hxz
            have hle := length_le_of_bruhat cs z.property.2
            have hdiff : rankDifference cs z.val y < n := by
              dsimp [rankDifference] at hxy ⊢
              omega
            rw [ih _ hdiff z.val y rfl, sub_self, mul_zero]
          · simp
        have href : reflect (rankDifference cs x y) (RP.2 x y - SQ.2 x y) =
            RP.2 x y - SQ.2 x y := by
          rw [reflect_sub, hRP.reciprocity x y hcomp, hSQ.reciprocity x y hcomp,
            finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib]
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro z _
          rw [← hR, mul_sub]
        have hd1 := hRP.P_degree x y hcomp heq
        have hd2 := hSQ.P_degree x y hcomp heq
        have hdeg := natDegree_sub_le (RP.2 x y) (SQ.2 x y)
        have hzero := low_degree_reflect_eq_self (RP.2 x y - SQ.2 x y)
          (rankDifference cs x y) (by omega) href
        exact sub_eq_zero.mp hzero
    · rw [hRP.P_zero _ _ hcomp, hSQ.P_zero _ _ hcomp]

/-- Unique existence is still a separate obligation: this proves its
uniqueness half only, without postulating a normalized family. -/
theorem normalizedKL_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP = SQ :=
  Prod.ext (normalized_R_unique cs hRP hSQ) (normalized_P_unique cs hRP hSQ)


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Hecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


namespace Hecke

variable {C : Type*} [CommRing C]

theorem left_right_commute (cs : CoxeterSystem M W) (a : C) (i j : B) :
    Commute (left cs a i) (right cs a j) := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, right_basis, left_basis, map_add]
  by_cases heq : cs.simple i * w = w * cs.simple j
  · have heq' : cs.simple i * (w * cs.simple j) = w := by rw [← heq]; simp
    have heq'' : cs.simple i * w * cs.simple j = w := by simpa [mul_assoc] using heq'
    rw [heq', heq'']
    by_cases h : cs.length (cs.simple i * w) < cs.length w
    · have h' : cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      simp only [map_smul, right_basis, left_basis,
        heq, ite_eq_left h']
    · have h' : ¬cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      simp only [ite_eq_right h', map_zero, add_zero, heq]
  · have hl := left_descent_mul_simple_iff cs i j w heq
    have hr := right_descent_simple_mul_iff cs i j w heq
    simp only [hl, hr]
    by_cases hi : cs.length (cs.simple i * w) < cs.length w <;>
      by_cases hj : cs.length (w * cs.simple j) < cs.length w <;>
      simp only [hi, hj, ite_true, if_true, ite_false, if_false, map_zero, add_zero, map_smul,
        left_basis, right_basis, smul_add, smul_smul, mul_assoc] ;
      abel

/-- Acting on the identity along a reduced word gives exactly its standard
basis element. -/
theorem leftWord_one (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    leftWord cs a ω (basis 1) = basis (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : ¬cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    simp [Module.End.mul_apply, ih hω', hasc, cs.wordProd_cons]

theorem rightWord_one (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    rightWord cs a ω (basis 1) = basis (cs.wordProd ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) =
        cs.length (cs.simple i * cs.wordProd ω) := by
      rw [← cs.length_inv (cs.simple i * cs.wordProd ω)]
      simp [mul_inv_rev]
    have hasc : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω)⁻¹ := by
      rw [hlen, cs.length_inv]
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hasc' : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω) := by simpa using hasc
    simp [Module.End.mul_apply, ih hω', hasc', cs.wordProd_cons, mul_inv_rev]

theorem commute_rightWord (cs : CoxeterSystem M W) (a : C)
    {f : Module.End C (Space W C)} (h : ∀ i, Commute f (right cs a i)) (ω : List B) :
    Commute f (rightWord cs a ω) := by
  apply Commute.list_prod_right
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact h i

/-- The regular right action is cyclic, with cyclic vector the identity. -/
theorem commuting_ext (cs : CoxeterSystem M W) (a : C)
    {f g : Module.End C (Space W C)}
    (hf : ∀ i, Commute f (right cs a i))
    (hg : ∀ i, Commute g (right cs a i))
    (h : f (basis 1) = g (basis 1)) : f = g := by
  apply end_ext
  intro w
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced w⁻¹
  have hw : rightWord cs a ω (basis 1) = basis w := by
    rw [rightWord_one cs a hω, ← heq, inv_inv]
  rw [← hw]
  have hf' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs a hf ω).eq
  have hg' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs a hg ω).eq
  simp only [Module.End.mul_apply] at hf' hg'
  rw [h] at hf'
  exact hf'.trans hg'.symm

theorem leftWord_commute_right (cs : CoxeterSystem M W) (a : C) (ω : List B) (i : B) :
    Commute (leftWord cs a ω) (right cs a i) := by
  apply Commute.list_prod_left
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact left_right_commute cs a j i


theorem leftWord_independent (cs : CoxeterSystem M W) (a : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    leftWord cs a ω = leftWord cs a η := by
  apply commuting_ext cs a (leftWord_commute_right cs a ω)
    (leftWord_commute_right cs a η)
  rw [leftWord_one cs a hω, leftWord_one cs a hη, heq]

theorem wordUnit_independent (cs : CoxeterSystem M W) (a : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    wordUnit cs a ω = wordUnit cs a η := by
  apply Units.ext
  simpa using leftWord_independent cs a hω hη heq

theorem standardUnit_word (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    standardUnit cs a (cs.wordProd ω) = wordUnit cs a ω := by
  apply wordUnit_independent cs a (Classical.choose_spec (cs.exists_isReduced _)).1 hω
  exact (Classical.choose_spec (cs.exists_isReduced _)).2.symm

@[simp] theorem standardUnit_one (cs : CoxeterSystem M W) (a : C) :
    standardUnit cs a 1 = 1 := by
  have h := standardUnit_word cs a (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa [wordUnit] using h

@[simp] theorem standardUnit_basis_one (cs : CoxeterSystem M W) (a : C) (w : W) :
    (standardUnit cs a w).val (basis 1) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [standardUnit_word cs a hω, wordUnit_val, leftWord_one cs a hω]


theorem standardUnit_mul_simple (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (w * cs.simple i)) :
    standardUnit cs a (w * cs.simple i) = standardUnit cs a w * unit cs a i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ [i]) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_mul_simple (cs.wordProd ω) i
    simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
      List.length_singleton]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_singleton i, ← cs.wordProd_append, standardUnit_word cs a hred,
    standardUnit_word cs a hω]
  simp [wordUnit, List.map_append, List.prod_append]

@[simp] theorem barBasis_one (cs : CoxeterSystem M W) (a : C) :
    barBasis cs a 1 = basis 1 := by simp [barBasis]

theorem barBasis_simple_mul_ascent (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    barBasis cs a (cs.simple i * w) = leftInv cs a i (barBasis cs a w) := by
  have hasc' : cs.length w⁻¹ < cs.length (w⁻¹ * cs.simple i) := by
    have hlen : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
      rw [← cs.length_inv (cs.simple i * w)]
      simp [mul_inv_rev]
    simpa [hlen] using hasc
  simp only [barBasis, mul_inv_rev, cs.inv_simple,
    standardUnit_mul_simple cs a i w⁻¹ hasc', Units.val_mul,
    Module.End.mul_apply]
  rfl

theorem left_coeff (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) (x : W) :
    (left cs a i v) x = v (cs.simple i * x) +
      if cs.length (cs.simple i * x) < cs.length x then a * v x else 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, Finsupp.add_apply, hv, hv', mul_add]
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c = c • (basis w : Space W C) := by
      simp [basis, Finsupp.smul_single]
    rw [hc, map_smul, left_basis]
    have heq : cs.simple i * w = x ↔ w = cs.simple i * x := by
      constructor <;> intro h
      · rw [← h]; simp
      · rw [h]; simp
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, basis,
      Finsupp.single_apply, heq]
    by_cases h : w = x
    · subst w
      split_ifs <;> try contradiction
      all_goals simp only [Finsupp.single_eq_same, Finsupp.zero_apply,
        Finsupp.smul_apply, smul_eq_mul, mul_one, mul_zero] ; ring
    · simp only [h, ite_false, if_false, mul_zero]
      by_cases hd : cs.length (cs.simple i * w) < cs.length w <;>
        by_cases hd' : cs.length (cs.simple i * x) < cs.length x <;>
        simp [hd, hd', h]

theorem leftInv_coeff (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) (x : W) :
    (leftInv cs a i v) x = v (cs.simple i * x) -
      if cs.length (cs.simple i * x) < cs.length x then 0 else a * v x := by
  simp only [leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, left_coeff]
  split_ifs <;> ring

theorem simple_mul_le_ascent (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) (hy : cs.length y < cs.length (cs.simple i * y)) :
    BruhatLE cs (cs.simple i * x) (cs.simple i * y) := by
  have hx := le_upperSimple cs i (cs.simple i * x)
  rw [upperSimple_mul] at hx
  have hm := upperSimple_mono cs i hxy
  simp only [upperSimple, ite_eq_right (show ¬cs.length (cs.simple i * y) < cs.length y by omega)] at hm
  exact hx.trans hm

/-- Triangularity for the genuine reflection-generated order. -/
theorem barBasis_zero (cs : CoxeterSystem M W) (a : C) (x y : W)
    (hxy : ¬BruhatLE cs x y) : barBasis cs a y x = 0 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω generalizing x with
  | nil =>
    have hx : x ≠ 1 := fun h => hxy (h ▸ bruhat_refl cs 1)
    simp [basis, Ne.symm hx]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hle : BruhatLE cs (cs.wordProd ω) (cs.simple i * cs.wordProd ω) :=
      Relation.ReflTransGen.single ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    have hn : ¬BruhatLE cs x (cs.wordProd ω) := fun h => hxy (h.trans hle)
    have hn' : ¬BruhatLE cs (cs.simple i * x) (cs.wordProd ω) := by
      intro h
      have := simple_mul_le_ascent cs i h hasc
      simp only [cs.simple_mul_simple_cancel_left] at this
      exact hxy this
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs a i _ hasc, leftInv_coeff,
      ih x hω' hn, ih (cs.simple i * x) hω' hn']
    split_ifs <;> simp

@[simp] theorem barBasis_diagonal (cs : CoxeterSystem M W) (a : C) (y : W) :
    barBasis cs a y y = 1 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω with
  | nil => simp [basis]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs a i _ hasc, leftInv_coeff]
    simpa [hasc] using ih hω'

@[simp] theorem rTilde_diagonal (cs : CoxeterSystem M W) (x : W) :
    rTilde cs x x = 1 := barBasis_diagonal cs (-X) x

theorem rTilde_zero (cs : CoxeterSystem M W) (x y : W) (h : ¬BruhatLE cs x y) :
    rTilde cs x y = 0 := barBasis_zero cs (-X) x y h

theorem rTilde_recursion (cs : CoxeterSystem M W) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    rTilde cs x y = if cs.length (cs.simple i * x) < cs.length x then
      rTilde cs (cs.simple i * x) (cs.simple i * y)
      else rTilde cs (cs.simple i * x) (cs.simple i * y) + X * rTilde cs x (cs.simple i * y) := by
  have hasc : cs.length (cs.simple i * y) <
      cs.length (cs.simple i * (cs.simple i * y)) := by simpa using hy
  have hb := barBasis_simple_mul_ascent cs (-X : ℤ[X]) i (cs.simple i * y) hasc
  simp only [cs.simple_mul_simple_cancel_left] at hb
  unfold rTilde
  rw [hb, leftInv_coeff]
  split_ifs <;> ring


end Hecke


namespace HeckeQ

open Hecke (Space basis end_ext)
variable {C : Type*} [CommRing C]

theorem left_right_commute (cs : CoxeterSystem M W) (q : C) (i j : B) :
    Commute (left cs q i) (right cs q j) := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, right_basis, left_basis]
  by_cases heq : cs.simple i * w = w * cs.simple j
  · have heq' : cs.simple i * (w * cs.simple j) = w := by rw [← heq]; simp
    have heq'' : cs.simple i * w * cs.simple j = w := by simpa [mul_assoc] using heq'
    by_cases h : cs.length (cs.simple i * w) < cs.length w
    · have h' : cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      have hn : ¬cs.length w < cs.length (cs.simple i * w) := by omega
      have hn' : ¬cs.length w < cs.length (w * cs.simple j) := heq ▸ hn
      simp [h', map_add, map_smul, heq', hn', heq]
    · have h' : ¬cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      have hl : cs.length w < cs.length (cs.simple i * w) := by
        have := cs.length_simple_mul w i; omega
      have hl' : cs.length w < cs.length (w * cs.simple j) := heq ▸ hl
      simp [h', heq', hl', heq]
  · have hl := left_descent_mul_simple_iff cs i j w heq
    have hr := right_descent_simple_mul_iff cs i j w heq
    have hr' : cs.length (cs.simple i * (w * cs.simple j)) <
        cs.length (cs.simple i * w) ↔ cs.length (w * cs.simple j) < cs.length w := by
      simpa only [mul_assoc] using hr
    by_cases hi : cs.length (cs.simple i * w) < cs.length w <;>
      by_cases hj : cs.length (w * cs.simple j) < cs.length w <;>
      simp only [hi, hj, ite_true, if_true, ite_false, if_false, map_add, map_smul,
        left_basis, right_basis, hl, hr', mul_assoc, smul_add, smul_smul] ;
      module

/-- Acting on the identity along q reduced word gives exactly its standard
basis element. -/
theorem leftWord_one (cs : CoxeterSystem M W) (q : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    leftWord cs q ω (basis 1) = basis (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : ¬cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    simp [Module.End.mul_apply, ih hω', hasc, cs.wordProd_cons]

theorem rightWord_one (cs : CoxeterSystem M W) (q : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    rightWord cs q ω (basis 1) = basis (cs.wordProd ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) =
        cs.length (cs.simple i * cs.wordProd ω) := by
      rw [← cs.length_inv (cs.simple i * cs.wordProd ω)]
      simp [mul_inv_rev]
    have hasc : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω)⁻¹ := by
      rw [hlen, cs.length_inv]
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hasc' : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω) := by simpa using hasc
    simp [Module.End.mul_apply, ih hω', hasc', cs.wordProd_cons, mul_inv_rev]

theorem commute_rightWord (cs : CoxeterSystem M W) (q : C)
    {f : Module.End C (Space W C)} (h : ∀ i, Commute f (right cs q i)) (ω : List B) :
    Commute f (rightWord cs q ω) := by
  apply Commute.list_prod_right
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact h i

/-- The regular right action is cyclic, with cyclic vector the identity. -/
theorem commuting_ext (cs : CoxeterSystem M W) (q : C)
    {f g : Module.End C (Space W C)}
    (hf : ∀ i, Commute f (right cs q i))
    (hg : ∀ i, Commute g (right cs q i))
    (h : f (basis 1) = g (basis 1)) : f = g := by
  apply end_ext
  intro w
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced w⁻¹
  have hw : rightWord cs q ω (basis 1) = basis w := by
    rw [rightWord_one cs q hω, ← heq, inv_inv]
  rw [← hw]
  have hf' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs q hf ω).eq
  have hg' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs q hg ω).eq
  simp only [Module.End.mul_apply] at hf' hg'
  rw [h] at hf'
  exact hf'.trans hg'.symm

theorem leftWord_commute_right (cs : CoxeterSystem M W) (q : C) (ω : List B) (i : B) :
    Commute (leftWord cs q ω) (right cs q i) := by
  apply Commute.list_prod_left
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact left_right_commute cs q j i


theorem leftWord_independent (cs : CoxeterSystem M W) (q : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    leftWord cs q ω = leftWord cs q η := by
  apply commuting_ext cs q (leftWord_commute_right cs q ω)
    (leftWord_commute_right cs q η)
  rw [leftWord_one cs q hω, leftWord_one cs q hη, heq]

theorem wordUnit_independent (cs : CoxeterSystem M W) (q : Cˣ) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    wordUnit cs q ω = wordUnit cs q η := by
  apply Units.ext
  simpa using leftWord_independent cs (q : C) hω hη heq

theorem standardUnit_word (cs : CoxeterSystem M W) (q : Cˣ) {ω : List B}
    (hω : cs.IsReduced ω) :
    standardUnit cs q (cs.wordProd ω) = wordUnit cs q ω := by
  apply wordUnit_independent cs q (Classical.choose_spec (cs.exists_isReduced _)).1 hω
  exact (Classical.choose_spec (cs.exists_isReduced _)).2.symm

@[simp] theorem standardUnit_one (cs : CoxeterSystem M W) (q : Cˣ) :
    standardUnit cs q 1 = 1 := by
  have h := standardUnit_word cs q (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa [wordUnit] using h

@[simp] theorem standardUnit_basis_one (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    (standardUnit cs q w).val (basis 1) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [standardUnit_word cs q hω, wordUnit_val, leftWord_one cs (q : C) hω]


theorem standardUnit_mul_simple (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (w * cs.simple i)) :
    standardUnit cs q (w * cs.simple i) = standardUnit cs q w * unit cs q i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ [i]) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_mul_simple (cs.wordProd ω) i
    simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
      List.length_singleton]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_singleton i, ← cs.wordProd_append, standardUnit_word cs q hred,
    standardUnit_word cs q hω]
  simp [wordUnit, List.map_append, List.prod_append]

@[simp] theorem barBasis_one (cs : CoxeterSystem M W) (q : Cˣ) :
    barBasis cs q 1 = basis 1 := by simp [barBasis]

theorem barBasis_simple_mul_ascent (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    barBasis cs q (cs.simple i * w) = leftInv cs q i (barBasis cs q w) := by
  have hasc' : cs.length w⁻¹ < cs.length (w⁻¹ * cs.simple i) := by
    have hlen : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
      rw [← cs.length_inv (cs.simple i * w)]
      simp [mul_inv_rev]
    simpa [hlen] using hasc
  simp only [barBasis, mul_inv_rev, cs.inv_simple,
    standardUnit_mul_simple cs q i w⁻¹ hasc', Units.val_mul,
    Module.End.mul_apply]
  rfl


theorem leftInv_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W) :
    leftInv cs q i (barBasis cs q w) =
      if cs.length (cs.simple i * w) < cs.length w then
        (↑q⁻¹ : C) • barBasis cs q (cs.simple i * w) +
          ((↑q⁻¹ : C) - 1) • barBasis cs q w
      else barBasis cs q (cs.simple i * w) := by
  by_cases h : cs.length (cs.simple i * w) < cs.length w
  · have hasc : cs.length (cs.simple i * w) <
        cs.length (cs.simple i * (cs.simple i * w)) := by simpa using h
    have hb := barBasis_simple_mul_ascent cs q i (cs.simple i * w) hasc
    simp only [cs.simple_mul_simple_cancel_left] at hb
    have hl : left cs (q : C) i (barBasis cs q w) = barBasis cs q (cs.simple i * w) := by
      rw [hb, ← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
    rw [ite_eq_left h, leftInv_apply, hl, smul_sub, smul_smul]
    have hscalar : (↑q⁻¹ : C) * ((q : C) - 1) = 1 - (↑q⁻¹ : C) := by
      rw [mul_sub, q.inv_mul, mul_one]
    rw [hscalar, sub_smul, one_smul]
    module
  · have hasc : cs.length w < cs.length (cs.simple i * w) := by
      have := cs.length_simple_mul w i
      omega
    rw [ite_eq_right h, barBasis_simple_mul_ascent cs q i w hasc]

/-- Linear intertwining, before specializing coefficients to a Laurent ring. -/
theorem barLinear_left (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    barLinear cs q * left cs (↑q⁻¹ : C) i = leftInv cs q i * barLinear cs q := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, leftInv_barBasis, barLinear_basis]
  split_ifs <;> simp

theorem barLinear_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) :
    barLinear cs q (leftInv cs q⁻¹ i v) = left cs (q : C) i (barLinear cs q v) := by
  have h := congrArg (fun f : Module.End C (Space W C) => f (leftInv cs q⁻¹ i v))
    (barLinear_left cs q i)
  simp only [Module.End.mul_apply] at h
  have hv : left cs (↑q⁻¹ : C) i (leftInv cs q⁻¹ i v) = v := by
    rw [← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
  rw [hv] at h
  have h' := congrArg (left cs (q : C) i) h
  have hl (t : Space W C) : left cs (q : C) i (leftInv cs q i t) = t := by
    rw [← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
  simpa only [hl] using h'.symm

/-- Applying coefficient inversion and the Hecke bar twice is the identity. -/
theorem barLinear_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    barLinear cs q (barBasis cs q⁻¹ w) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q⁻¹ i _ hasc,
      barLinear_leftInv, ih hω', left_basis, ite_eq_right (by omega)]

theorem leftInv_coeff (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) (x : W) :
    leftInv cs q i v x =
      if cs.length (cs.simple i * x) < cs.length x then (↑q⁻¹ : C) * v (cs.simple i * x)
      else v (cs.simple i * x) + ((↑q⁻¹ : C) - 1) * v x := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, Finsupp.add_apply, hv, hv']
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c = c • (basis w : Space W C) := by
      simp [basis, Finsupp.smul_single]
    rw [hc, map_smul, leftInv_basis]
    by_cases h : w = cs.simple i * x
    · subst w
      have hd : cs.length (cs.simple i * (cs.simple i * x)) < cs.length (cs.simple i * x) ↔
          ¬ cs.length (cs.simple i * x) < cs.length x := by
        simp only [cs.simple_mul_simple_cancel_left]
        have := cs.length_simple_mul x i
        omega
      have hn : cs.simple i * x ≠ x := by
        intro he
        have := cs.length_simple_mul x i
        rw [he] at this
        omega
      simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
        cs.simple_mul_simple_cancel_left, hn, ite_false, if_false]
      have hlength := cs.length_simple_mul x i
      split_ifs <;> try omega
      all_goals simp [Ne.symm hn] <;> try ring
    · have hn : cs.simple i * w ≠ x := by
        intro he
        apply h
        rw [← he]
        simp
      by_cases hw : w = x
      · subst w
        simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
          Ne.symm hn, ite_false, if_false, ]
        split_ifs <;> simp [Ne.symm hn] ; try ring
      · simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
          h, hw, ite_false, if_false]
        split_ifs <;> simp [hn, hw]

/-- Triangularity in the actual Bruhat order. -/
theorem barBasis_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : ¬BruhatLE cs x y) : barBasis cs q y x = 0 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω generalizing x with
  | nil =>
    have hx : x ≠ 1 := fun h => hxy (h ▸ bruhat_refl cs 1)
    simp [basis, Ne.symm hx]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hle : BruhatLE cs (cs.wordProd ω) (cs.simple i * cs.wordProd ω) :=
      Relation.ReflTransGen.single ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    have hn : ¬BruhatLE cs x (cs.wordProd ω) := fun h => hxy (h.trans hle)
    have hn' : ¬BruhatLE cs (cs.simple i * x) (cs.wordProd ω) := by
      intro h
      have := Hecke.simple_mul_le_ascent cs i h hasc
      simp only [cs.simple_mul_simple_cancel_left] at this
      exact hxy this
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q i _ hasc, leftInv_coeff,
      ih x hω' hn, ih (cs.simple i * x) hω' hn']
    split_ifs <;> simp

@[simp] theorem barBasis_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (y : W) :
    barBasis cs q y y = (↑q⁻¹ : C) ^ cs.length y := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω with
  | nil => simp [basis]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hlen : cs.length (cs.simple i * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
      have := cs.length_simple_mul (cs.wordProd ω) i
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q i _ hasc, leftInv_coeff]
    rw [cs.simple_mul_simple_cancel_left, ite_eq_left hasc, ih hω', hlen, pow_succ]
    ring

@[simp] theorem rValue_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    rValue cs q x x = 1 := by
  rw [rValue, barBasis_diagonal, ← mul_pow, ← mul_pow]
  simp

theorem rValue_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : ¬BruhatLE cs x y) : rValue cs q x y = 0 := by
  rw [rValue, barBasis_zero cs q x y hxy, mul_zero]

/-- The classical R recursion holds for *every* left descent, by Hecke
operator independence. This is the consistency obligation for actual R. -/
theorem rValue_recursion (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    rValue cs q x y =
      if cs.length (cs.simple i * x) < cs.length x then
        rValue cs q (cs.simple i * x) (cs.simple i * y)
      else ((q : C) - 1) * rValue cs q x (cs.simple i * y) +
        (q : C) * rValue cs q (cs.simple i * x) (cs.simple i * y) := by
  have hasc : cs.length (cs.simple i * y) <
      cs.length (cs.simple i * (cs.simple i * y)) := by simpa using hy
  have hb := barBasis_simple_mul_ascent cs q i (cs.simple i * y) hasc
  simp only [cs.simple_mul_simple_cancel_left] at hb
  have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
    have := cs.length_simple_mul y i
    omega
  have hu : (q : C) * (↑q⁻¹ : C) = 1 := q.val_inv
  by_cases hx : cs.length (cs.simple i * x) < cs.length x
  · have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [ite_eq_left hx]
    simp only [rValue, hb, leftInv_coeff, ite_eq_left hx]
    rw [hxlen, hylen]
    simp only [pow_succ]
    linear_combination ((-1 : C) ^ cs.length (cs.simple i * x) *
      (-(q : C)) ^ cs.length (cs.simple i * y) *
      barBasis cs q (cs.simple i * y) (cs.simple i * x)) * hu
  · have hxlen : cs.length (cs.simple i * x) = cs.length x + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [ite_eq_right hx]
    simp only [rValue, hb, leftInv_coeff, ite_eq_right hx]
    rw [hxlen, hylen]
    simp only [pow_succ]
    linear_combination -((-1 : C) ^ cs.length x *
      (-(q : C)) ^ cs.length (cs.simple i * y) *
      barBasis cs q (cs.simple i * y) x) * hu

end HeckeQ

namespace HeckeQ

open Hecke (Space basis)
variable {C : Type*} [CommRing C]

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions
theorem bar_coeff_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y, barBasis cs q z x * barBasis cs q⁻¹ y z =
      if x = y then 1 else 0 := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_barBasis cs q y)
  rw [barLinear, Finsupp.linearCombination_apply, Finsupp.sum_apply] at h
  have hs : (barBasis cs q⁻¹ y).support ⊆ lowerFinset cs y := by
    intro z hz
    apply (mem_lowerFinset cs y z).mpr
    by_contra hn
    exact Finsupp.mem_support_iff.mp hz (barBasis_zero cs _ _ _ hn)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp), basis, Finsupp.single_apply] at h
  simpa only [Finsupp.smul_apply, smul_eq_mul, mul_comm, eq_comm] using h

theorem rValue_inverse_factor (cs : CoxeterSystem M W) (q : Cˣ) (x z y : W) :
    rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y =
      ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by
  simp only [rValue]
  rw [neg_pow (q : C), neg_pow (↑q⁻¹ : C)]
  calc
    _ = ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (((-1 : C) * (-1)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by simp only [mul_pow]; ring
    _ = _ := by simp

/-- The exact R-kernel identity, before specialization to polynomials. -/
theorem rValue_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y = if x = y then 1 else 0 := by
  classical
  simp_rw [rValue_inverse_factor]
  rw [← Finset.mul_sum, bar_coeff_inverse]
  split_ifs with h
  · subst y
    rw [← mul_pow]
    simp
  · simp

end HeckeQ

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions
/-- Reflection of a bounded-degree polynomial evaluated at an actual unit. -/
theorem eval₂_reflect_unit {C : Type*} [CommRing C] (q : Cˣ)
    (p : ℤ[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (reflect d p) =
      (q : C) ^ d * Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p := by
  let := q⁻¹.invertible
  have h := Polynomial.eval₂_reflect_mul_pow (Int.castRingHom C) (↑q⁻¹ : C) d p hp
  simp only [invOf_units, inv_inv] at h
  have h' := congrArg (fun a : C => a * (q : C) ^ d) h
  calc
    _ = Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p * (q : C) ^ d := by
      simpa only [mul_assoc, ← mul_pow, q.inv_mul, one_pow, mul_one] using h'
    _ = _ := mul_comm _ _


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_OrdinaryR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Construction of ordinary R-polynomials, left-simple recursion, degree bounds and inverse kernels.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace OrdinaryR

open LaurentPolynomial

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
/-- Polynomiality of the R-values is proved from the Hecke-derived recursion. -/
theorem rValue_polynomial (cs : CoxeterSystem M W) (x y : W) :
    ∃ p : ℤ[X], p.toLaurent = HeckeQ.rValue cs variableUnit x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      ∃ p : ℤ[X], p.toLaurent = HeckeQ.rValue cs variableUnit x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        exact ⟨1, by simp⟩
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        exact ⟨0, by rw [HeckeQ.rValue_zero cs _ _ _ hn]; simp⟩
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      obtain ⟨p, hp⟩ := ih _ hlt _ rfl x
      obtain ⟨r, hr⟩ := ih _ hlt _ rfl (cs.simple i * x)
      rw [HeckeQ.rValue_recursion cs variableUnit x y i hi]
      split_ifs
      · exact ⟨r, hr⟩
      · refine ⟨(X - 1) * p + X * r, ?_⟩
        simp [hp, hr]

@[simp] theorem toLaurent_polynomial (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).toLaurent = HeckeQ.rValue cs variableUnit x y := by
  obtain ⟨p, hp⟩ := rValue_polynomial cs x y
  rw [polynomial, ← hp, Polynomial.trunc_toLaurent]

@[simp] theorem polynomial_diagonal (cs : CoxeterSystem M W) (x : W) :
    polynomial cs x x = 1 := by
  apply Polynomial.toLaurent_injective
  simp

theorem polynomial_zero (cs : CoxeterSystem M W) (x y : W)
    (hxy : ¬ BruhatLE cs x y) : polynomial cs x y = 0 := by
  apply Polynomial.toLaurent_injective
  simp [HeckeQ.rValue_zero cs _ x y hxy]

theorem polynomial_recursion (cs : CoxeterSystem M W) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    polynomial cs x y =
      if cs.length (cs.simple i * x) < cs.length x then
        polynomial cs (cs.simple i * x) (cs.simple i * y)
      else (X - 1) * polynomial cs x (cs.simple i * y) +
        X * polynomial cs (cs.simple i * x) (cs.simple i * y) := by
  apply Polynomial.toLaurent_injective
  rw [toLaurent_polynomial, HeckeQ.rValue_recursion cs variableUnit x y i hy]
  split_ifs <;> simp

/-- Specializing the honest integral polynomial recovers the Hecke R-value
at every unit parameter, not just the Laurent indeterminate. -/
theorem polynomial_eval {C : Type*} [CommRing C] (cs : CoxeterSystem M W)
    (q : Cˣ) (x y : W) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (polynomial cs x y) =
      HeckeQ.rValue cs q x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      Polynomial.eval₂ (Int.castRingHom C) (q : C) (polynomial cs x y) =
        HeckeQ.rValue cs q x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x; simp
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [polynomial_zero cs _ _ hn, HeckeQ.rValue_zero cs _ _ _ hn]
        simp
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [polynomial_recursion cs x y i hi, HeckeQ.rValue_recursion cs q x y i hi]
      split_ifs
      · exact ih _ hlt _ rfl (cs.simple i * x)
      · simp [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

/-- The degree bound needed for the classical polynomial reciprocity. -/
theorem polynomial_degree (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).natDegree ≤ rankDifference cs x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      (polynomial cs x y).natDegree ≤ rankDifference cs x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases hxy : BruhatLE cs x y
    · by_cases heq : x = y
      · subst x; simp [rankDifference]
      · have hlen := length_lt_of_bruhat_ne cs hxy heq
        have hone : y ≠ 1 := by
          intro h; subst y; simp at hlen
        obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hone
        have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
        have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
          have := cs.length_simple_mul y i
          omega
        rw [polynomial_recursion cs x y i hi]
        by_cases hx : cs.length (cs.simple i * x) < cs.length x
        · rw [ite_eq_left hx]
          have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
            have := cs.length_simple_mul x i
            omega
          have hn := ih _ hlt _ rfl (cs.simple i * x)
          simpa [rankDifference, hylen, hxlen] using hn
        · rw [ite_eq_right hx]
          have hxlen : cs.length (cs.simple i * x) = cs.length x + 1 := by
            have := cs.length_simple_mul x i
            omega
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · have hn := ih _ hlt _ rfl x
            have hp : (X - 1 : ℤ[X]).natDegree ≤ 1 := by
              exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
            refine Polynomial.natDegree_mul_le.trans ?_
            dsimp [rankDifference] at hn ⊢
            omega
          · by_cases hsy : BruhatLE cs (cs.simple i * x) (cs.simple i * y)
            · have hl := length_le_of_bruhat cs hsy
              have hn := ih _ hlt _ rfl (cs.simple i * x)
              refine Polynomial.natDegree_mul_le.trans ?_
              simp only [Polynomial.natDegree_X]
              dsimp [rankDifference] at hn ⊢
              omega
            · rw [polynomial_zero cs _ _ hsy, mul_zero]
              simp
    · rw [polynomial_zero cs _ _ hxy]
      simp

/-- Polynomial R is a kernel for the length-reflection involution. -/
theorem polynomial_kernel (cs : CoxeterSystem M W) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y) =
      if x = y then 1 else 0 := by
  classical
  apply Polynomial.toLaurent_injective
  rw [map_sum]
  have h := HeckeQ.rValue_inverse cs variableUnit x y
  have heq : ∀ z ∈ lowerFinset cs y,
      (polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y)).toLaurent =
      HeckeQ.rValue cs variableUnit x z *
        (variableUnit : LaurentPolynomial ℤ) ^ cs.length y *
        (↑variableUnit⁻¹ : LaurentPolynomial ℤ) ^ cs.length z *
        HeckeQ.rValue cs variableUnit⁻¹ z y := by
    intro z hz
    have hle := length_le_of_bruhat cs ((mem_lowerFinset cs y z).mp hz)
    rw [map_mul, toLaurent_polynomial, ← eval_variableUnit,
      eval₂_reflect_unit _ _ _ (polynomial_degree cs z y), polynomial_eval]
    have hlen : cs.length y = rankDifference cs z y + cs.length z := by
      dsimp [rankDifference]; omega
    rw [hlen, pow_add]
    simp only [mul_assoc]
    rw [← mul_assoc ((variableUnit : LaurentPolynomial ℤ) ^ cs.length z),
      ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [Finset.sum_congr rfl heq, h]
  split_ifs <;> simp

end OrdinaryR

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
theorem rankDifference_add (cs : CoxeterSystem M W) {x z y : W}
    (hxz : BruhatLE cs x z) (hzy : BruhatLE cs z y) :
    rankDifference cs x y = rankDifference cs x z + rankDifference cs z y := by
  have := length_le_of_bruhat cs hxz
  have := length_le_of_bruhat cs hzy
  dsimp [rankDifference]
  omega

theorem reflect_finset_sum {A : Type*} (s : Finset A) (d : ℕ) (f : A → ℤ[X]) :
    reflect d (∑ a ∈ s, f a) = ∑ a ∈ s, reflect d (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, reflect_add, ih]

namespace OrdinaryR

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
theorem polynomial_kernel_reverse (cs : CoxeterSystem M W) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      reflect (rankDifference cs x z) (polynomial cs x z) * polynomial cs z y =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : BruhatLE cs x y
  · have h := congrArg (reflect (rankDifference cs x y)) (polynomial_kernel cs x y)
    rw [reflect_finset_sum] at h
    have heq : ∀ z ∈ lowerFinset cs y,
        reflect (rankDifference cs x y)
          (polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y)) =
        reflect (rankDifference cs x z) (polynomial cs x z) * polynomial cs z y := by
      intro z hz
      by_cases hxz : BruhatLE cs x z
      · rw [rankDifference_add cs hxz ((mem_lowerFinset cs y z).mp hz),
          reflect_mul _ _ (polynomial_degree cs x z)
            (Polynomial.natDegree_reflect_le.trans (max_le le_rfl (polynomial_degree cs z y))), reflect_reflect]
      · rw [polynomial_zero cs x z hxz, zero_mul, reflect_zero, reflect_zero, zero_mul]
    rw [Finset.sum_congr rfl heq] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    split_ifs with he
    · subst y
      simp [rankDifference]
    · simp
  · rw [ite_eq_right (by intro he; subst y; exact hxy (bruhat_refl cs x))]
    apply Finset.sum_eq_zero
    intro z hz
    have hxz : ¬BruhatLE cs x z := fun hxz =>
      hxy (bruhat_trans cs hxz ((mem_lowerFinset cs y z).mp hz))
    rw [polynomial_zero cs x z hxz, reflect_zero, zero_mul]

end OrdinaryR

theorem sum_proper_eq_sub (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (f : W → ℤ[X])
    (hzero : ∀ z, ¬BruhatLE cs x z → f z = 0) :
    ∑ z ∈ properIntervalFinset cs x y, f z =
      (∑ z ∈ lowerFinset cs y, f z) - f x := by
  classical
  rw [← Finset.sum_erase_eq_sub ((mem_lowerFinset cs y x).mpr hxy)]
  apply Finset.sum_subset
  · intro z hz
    have hz := (mem_properIntervalFinset cs x y z).mp hz
    exact Finset.mem_erase.mpr ⟨Ne.symm hz.2.2, (mem_lowerFinset cs y z).mpr hz.1⟩
  · intro z hz hnot
    apply hzero
    intro hxz
    have hz := Finset.mem_erase.mp hz
    exact hnot ((mem_properIntervalFinset cs x y z).mpr
      ⟨(mem_lowerFinset cs y z).mp hz.2, hxz, Ne.symm hz.1⟩)


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CanonicalKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical low-part construction, strict halfdegree, reciprocity and uniqueness; certification of the selected polynomials and interval ranks.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace CanonicalP

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_2
theorem lowPart_degree (d : ℕ) (p : ℤ[X]) (hd : 0 < d) :
    2 * (lowPart d p).natDegree < d := by
  have h : (lowPart d p).natDegree ≤ (d - 1) / 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_lowPart, ite_eq_right (by omega)]
  omega

/-- Solve the anti-reciprocal defect with the required strict degree bound. -/
theorem lowPart_solution (d : ℕ) (p : ℤ[X]) (hanti : reflect d p = -p) :
    reflect d (-lowPart d p) = -lowPart d p + p := by
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun f : ℤ[X] => f.coeff n) hanti
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg] at hc
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg, Polynomial.coeff_add,
    coeff_lowPart]
  by_cases hn : n ≤ d
  · rw [Polynomial.revAt_le hn] at hc ⊢
    by_cases hlow : 2 * n < d
    · rw [ite_eq_left hlow, ite_eq_right (by omega)]
      ring
    · rw [ite_eq_right hlow]
      by_cases hmid : 2 * n = d
      · have hm : d - n = n := by omega
        rw [hm, ite_eq_right hlow]
        rw [hm] at hc
        linarith
      · rw [ite_eq_left (by omega)]
        linarith
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)] at hc ⊢
    rw [ite_eq_right (by omega)]
    linarith

theorem polynomial_zero (cs : CoxeterSystem M W) (x y : W)
    (hxy : ¬BruhatLE cs x y) : polynomial cs x y = 0 := by
  rw [polynomial, ite_eq_right hxy]

theorem polynomial_recursion (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    polynomial cs x y = -lowPart (rankDifference cs x y) (defect cs x y) := by
  rw [polynomial, ite_eq_left hxy, ite_eq_right hne]
  rw [Finset.sum_attach _ (fun z => OrdinaryR.polynomial cs x z * polynomial cs z y), defect]

theorem polynomial_strict_degree (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    2 * (polynomial cs x y).natDegree < rankDifference cs x y := by
  rw [polynomial_recursion cs x y hxy hne, Polynomial.natDegree_neg]
  apply lowPart_degree
  have := length_lt_of_bruhat_ne cs hxy hne
  dsimp [rankDifference]
  omega

theorem polynomial_degree (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).natDegree ≤ rankDifference cs x y := by
  by_cases hxy : BruhatLE cs x y
  · by_cases hne : x = y
    · subst y
      simp
    · have := polynomial_strict_degree cs x y hxy hne
      omega
  · rw [polynomial_zero cs x y hxy]
    simp

theorem defect_full_sum (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    defect cs x y = (∑ z ∈ lowerFinset cs y,
      OrdinaryR.polynomial cs x z * polynomial cs z y) - polynomial cs x y := by
  rw [defect, sum_proper_eq_sub cs x y hxy]
  · simp
  · intro z hz
    rw [OrdinaryR.polynomial_zero cs x z hz, zero_mul]

theorem reversed_kernel_on_lower (cs : CoxeterSystem M W) (x y t : W)
    (hty : BruhatLE cs t y) :
    ∑ z ∈ lowerFinset cs y,
      reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
        OrdinaryR.polynomial cs z t = if x = t then 1 else 0 := by
  classical
  rw [← OrdinaryR.polynomial_kernel_reverse cs x t]
  symm
  apply Finset.sum_subset
  · intro z hz
    exact (mem_lowerFinset cs y z).mpr
      (bruhat_trans cs ((mem_lowerFinset cs t z).mp hz) hty)
  · intro z hz hnt
    have hzt : ¬BruhatLE cs z t := fun h => hnt ((mem_lowerFinset cs t z).mpr h)
    rw [OrdinaryR.polynomial_zero cs z t hzt, mul_zero]

theorem reversed_kernel_on_proper (cs : CoxeterSystem M W) (x y t : W)
    (hxy : BruhatLE cs x y) (hty : BruhatLE cs t y) :
    ∑ z ∈ properIntervalFinset cs x y,
      reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
        OrdinaryR.polynomial cs z t =
      (if x = t then 1 else 0) - OrdinaryR.polynomial cs x t := by
  rw [sum_proper_eq_sub cs x y hxy]
  · rw [reversed_kernel_on_lower cs x y t hty]
    simp [rankDifference]
  · intro z hz
    rw [OrdinaryR.polynomial_zero cs x z hz, reflect_zero, zero_mul]

/-- The reciprocity equation is a theorem of the lower-half construction. -/
theorem polynomial_reciprocity (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    reflect (rankDifference cs x y) (polynomial cs x y) =
      ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z * polynomial cs z y := by
  classical
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → BruhatLE cs x y →
      reflect (rankDifference cs x y) (polynomial cs x y) =
        ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z * polynomial cs z y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases hne : x = y
    · subst y
      rw [polynomial_diagonal]
      simp only [rankDifference, Nat.sub_self, Polynomial.reflect_one, pow_zero]
      symm
      rw [Finset.sum_eq_single x]
      · simp
      · intro z hz hzx
        have hnxz : ¬BruhatLE cs x z := fun hxz =>
          hzx (bruhat_antisymm cs ((mem_lowerFinset cs x z).mp hz) hxz)
        rw [OrdinaryR.polynomial_zero cs x z hnxz, zero_mul]
      · intro hmiss
        exact (hmiss ((mem_lowerFinset cs x x).mpr (bruhat_refl cs x))).elim
    · have hanti : reflect (rankDifference cs x y) (defect cs x y) = -defect cs x y := by
        rw [defect, reflect_finset_sum]
        have heq : ∀ z ∈ properIntervalFinset cs x y,
            reflect (rankDifference cs x y)
              (OrdinaryR.polynomial cs x z * polynomial cs z y) =
            reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
              (∑ t ∈ lowerFinset cs y, OrdinaryR.polynomial cs z t * polynomial cs t y) := by
          intro z hz
          have hz := (mem_properIntervalFinset cs x y z).mp hz
          have hlt : rankDifference cs z y < n := by
            have := length_lt_of_bruhat_ne cs hz.2.1 hz.2.2
            have := length_le_of_bruhat cs hz.1
            dsimp [rankDifference] at hn ⊢
            omega
          rw [rankDifference_add cs hz.2.1 hz.1,
            reflect_mul _ _ (OrdinaryR.polynomial_degree cs x z) (polynomial_degree cs z y),
            ih _ hlt z y rfl hz.1]
        rw [Finset.sum_congr rfl heq]
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul]
        have hkernel : ∀ t ∈ lowerFinset cs y,
            (∑ z ∈ properIntervalFinset cs x y,
              reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
                OrdinaryR.polynomial cs z t) * polynomial cs t y =
            ((if x = t then 1 else 0) - OrdinaryR.polynomial cs x t) * polynomial cs t y := by
          intro t ht
          rw [reversed_kernel_on_proper cs x y t hxy ((mem_lowerFinset cs y t).mp ht)]
        rw [Finset.sum_congr rfl hkernel]
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        have hdelta : (∑ t ∈ lowerFinset cs y,
            (if x = t then (1 : ℤ[X]) else 0) * polynomial cs t y) = polynomial cs x y := by
          rw [Finset.sum_eq_single x]
          · simp
          · intro t ht htx
            simp [Ne.symm htx]
          · intro hmiss
            exact (hmiss ((mem_lowerFinset cs y x).mpr hxy)).elim
        rw [hdelta]
        change polynomial cs x y - (∑ z ∈ lowerFinset cs y,
          OrdinaryR.polynomial cs x z * polynomial cs z y) = -defect cs x y
        rw [defect_full_sum cs x y hxy]
        ring
      rw [polynomial_recursion cs x y hxy hne, lowPart_solution _ _ hanti]
      rw [← polynomial_recursion cs x y hxy hne, defect_full_sum cs x y hxy]
      ring

end CanonicalP

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_2
/-- Finitely supported interval sums agree with the lower-ideal sums used in
our construction; all incomparable summands are literally zero. -/
theorem normalized_interval_sum (cs : CoxeterSystem M W) (x y : W) :
    (∑ᶠ z : Interval cs x y,
      OrdinaryR.polynomial cs x z.val * CanonicalP.polynomial cs z.val y) =
    ∑ z ∈ lowerFinset cs y,
      OrdinaryR.polynomial cs x z * CanonicalP.polynomial cs z y := by
  classical
  let := interval_finite cs x y
  let : Fintype (Interval cs x y) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hsum := Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs x y)))
    ((lowerFinset cs y).filter (fun z => BruhatLE cs x z))
    (fun z => by simp only [Finset.mem_filter, mem_lowerFinset]; exact and_comm)
    (fun z => OrdinaryR.polynomial cs x z * CanonicalP.polynomial cs z y)
  refine hsum.symm.trans ?_
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hnxz : ¬BruhatLE cs x z := fun hxz => hnot (Finset.mem_filter.mpr ⟨hz, hxz⟩)
  rw [OrdinaryR.polynomial_zero cs x z hnxz, zero_mul]

/-- The selected polynomials really exist with the classical equal-parameter
normalization. This is a construction, not an extra hypothesis. -/
theorem constructed_normalizedKL (cs : CoxeterSystem M W) :
    NormalizedKL cs (OrdinaryR.polynomial cs, CanonicalP.polynomial cs) where
  R_diagonal := OrdinaryR.polynomial_diagonal cs
  R_zero := OrdinaryR.polynomial_zero cs
  R_recursion := OrdinaryR.polynomial_recursion cs
  P_diagonal := CanonicalP.polynomial_diagonal cs
  P_zero := CanonicalP.polynomial_zero cs
  P_degree := CanonicalP.polynomial_strict_degree cs
  reciprocity := by
    intro x y hxy
    rw [normalized_interval_sum]
    exact CanonicalP.polynomial_reciprocity cs x y hxy

theorem normalizedKL_existsUnique (cs : CoxeterSystem M W) :
    ∃! RP : PolynomialFamilies W, NormalizedKL cs RP := by
  refine ⟨(OrdinaryR.polynomial cs, CanonicalP.polynomial cs), constructed_normalizedKL cs, ?_⟩
  intro RP hRP
  exact normalizedKL_unique cs hRP (constructed_normalizedKL cs)

theorem klFamilies_spec (cs : CoxeterSystem M W) : NormalizedKL cs (klFamilies cs) := by
  exact Classical.epsilon_spec (normalizedKL_existsUnique cs).exists

theorem klFamilies_eq_constructed (cs : CoxeterSystem M W) :
    klFamilies cs = (OrdinaryR.polynomial cs, CanonicalP.polynomial cs) :=
  normalizedKL_unique cs (klFamilies_spec cs) (constructed_normalizedKL cs)

theorem rPolynomial_eq_constructed (cs : CoxeterSystem M W) (x y : W) :
    rPolynomial cs x y = OrdinaryR.polynomial cs x y := by
  simp only [rPolynomial, klFamilies_eq_constructed]


end KLInvariance

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Dihedral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance.HeckeQ

universe uR vR
variable {B : Type uR} {W : Type vR} [Group W] {M : CoxeterMatrix B}
variable {C : Type*} [CommRing C]

@[simp] theorem dualR_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    dualR cs q x x = 1 := by
  rw [dualR, rValue_diagonal, mul_one, ← mul_pow]
  simp

end KLInvariance.HeckeQ

end

section

namespace KLInvariance
open Polynomial
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- The exact square-parameter normalization, proved from the two genuine
Hecke recurrences. Integer exponents let the formula include incomparable
pairs without silently changing the R-polynomial definition. -/
theorem rPolynomial_normalization {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0) (x y : W) :
    eval₂ (Int.castRingHom C) (v^2) (rPolynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) := by
  rw [rPolynomial_eq_constructed]
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
    eval₂ (Int.castRingHom C) (v^2) (OrdinaryR.polynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) from
    this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y=1
    · subst y
      by_cases hx : x=1
      · subst x; simp
      · have hn : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x=0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [OrdinaryR.polynomial_zero cs _ _ hn,Hecke.rTilde_zero cs _ _ hn]
        simp
    · obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i*y)<n := hy ▸ hi
      have hylen : cs.length (cs.simple i*y)+1=cs.length y := by
        have := cs.length_simple_mul y i; omega
      rw [OrdinaryR.polynomial_recursion cs x y i hi,Hecke.rTilde_recursion cs x y i hi]
      by_cases hx : cs.length (cs.simple i*x) < cs.length x
      · rw [ite_eq_left hx,ite_eq_left hx,ih _ hlt _ rfl (cs.simple i*x)]
        congr 2
        have := cs.length_simple_mul x i
        omega
      · rw [ite_eq_right hx,ite_eq_right hx]
        simp only [eval₂_add,eval₂_mul,eval₂_sub,eval₂_X,eval₂_one]
        rw [ih _ hlt _ rfl x,ih _ hlt _ rfl (cs.simple i*x)]
        have hxlen : cs.length (cs.simple i*x)=cs.length x+1 := by
          have := cs.length_simple_mul x i; omega
        have h1 : (cs.length (cs.simple i*y) : ℤ)-cs.length x =
            ((cs.length y : ℤ)-cs.length x)-1 := by omega
        have h2 : (cs.length (cs.simple i*y) : ℤ)-cs.length (cs.simple i*x) =
            ((cs.length y : ℤ)-cs.length x)-2 := by omega
        rw [h1,h2,zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 1,
          zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 2]
        simp only [zpow_ofNat]
        field_simp [hv]
        ; ring

end KLInvariance


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.piPiece_finite _root_.OAI.KLInvariance.Graded.subPiece_finite _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/

section

namespace KLInvariance.Hilbert

/-- Sum over all monomials in finitely many variables, before grouping by degree. -/
theorem hasSum_monomials (σ : Type*) [Fintype σ] {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ) := by
  classical
  apply Fintype.induction_empty_option (P := fun σ _ =>
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ))
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Fintype.card_congr e]
    apply (Equiv.piCongrLeft (fun _ : β => ℕ) e).hasSum_iff.mp
    convert ih using 1
    all_goals try with_reducible_and_instances rfl
    ext d
    simp only [Function.comp_apply, Equiv.piCongrLeft_apply]
    congr 1
    simpa using e.symm.sum_comp d
  · simp
  · intro α _ ih
    have hg := hasSum_geometric_of_lt_one hq hq1
    have hs := hg.summable.mul_of_nonneg ih.summable
      (fun _ => pow_nonneg hq _) (fun _ => pow_nonneg hq _)
    have hh := hg.mul ih hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hh
    simpa [Function.comp_def, Fintype.sum_option, pow_add, pow_succ, mul_comm] using he


lemma intWeight_eq_natWeight {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) d : ℕ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]

lemma polynomialGrading_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Graded.polynomialGrading k σ n =
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℕ)) n := by
  ext p
  change (∀ d, p.coeff d ≠ 0 →
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d = (n : ℤ)) ↔ _
  simp only [intWeight_eq_natWeight, Nat.cast_inj]
  rfl

instance polynomialPiece_finite (k : Type*) [Field k] (σ : Type*) [Finite σ] (n : ℤ) :
    Module.Finite k (Graded.polynomialGrading k σ n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [polynomialGrading_nat]
    exact Module.Finite.iff_fg.mpr
      (MvPolynomial.weightedHomogeneousSubmodule_fg k (fun _ : σ => 1) (by simp) m)
  · rw [Graded.polynomialGrading_negative k σ n (lt_of_not_ge hn)]
    infer_instance

lemma polynomial_finrank_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Module.finrank k (Graded.polynomialGrading k σ n) =
      Nat.card {d : σ →₀ ℕ // Finsupp.weight (fun _ => (1 : ℕ)) d = n} := by
  rw [polynomialGrading_nat, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k _)

lemma hasSum_finsupp_monomials (σ : Type*) [Fintype σ] {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ →₀ ℕ => q ^ Finsupp.weight (fun _ => (1 : ℕ)) d)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).hasSum_iff.mpr
    (hasSum_monomials σ hq hq1)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext d
  congr 1
  simp only [Finsupp.weight_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype d _ (by simp)

/-- The actual finite polynomial ring has Hilbert series `(1-q)⁻ᴺ`. -/
theorem hasSum_polynomial_nat (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (hasSum_finsupp_monomials σ hq hq1).tsum_fiberwise
    (Finsupp.weight (fun _ : σ => (1 : ℕ)))
  apply h.congr_fun
  intro n
  rw [polynomial_finrank_nat]
  have hf : (fun d : ↑((Finsupp.weight (R := ℕ) (fun _ : σ => (1 : ℕ))) ⁻¹' {n}) =>
      q ^ (Finsupp.weight (fun _ : σ => (1 : ℕ))) d.val) = fun _ => q^n := by
    funext d
    rw [show Finsupp.weight (fun _ : σ => (1 : ℕ)) d.val = n from d.property]
  rw [hf, tsum_const, nsmul_eq_mul]
  simp only [Set.preimage, Set.mem_singleton_iff]
  rfl


/-- Integer-indexed grading, including its zero negative pieces. -/
theorem hasSum_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  apply ((Nat.cast_injective : Function.Injective ((↑) : ℕ → ℤ)).hasSum_iff ?_).mp
  · simpa only [Function.comp_def, zpow_natCast] using hasSum_polynomial_nat k σ hq hq1
  · intro n hn
    have hn' : n < 0 := by
      by_contra h
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
      exact hn ⟨m, rfl⟩
    rw [Graded.polynomialGrading_negative k σ n hn']
    simp

end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

lemma shiftedPiece_finrank {ι : Type ui} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.finrank k (Graded.shiftedPiece 𝓐 d n) = ∑ i, Module.finrank k (𝓐 (n-d i)) := by
  rw [(shiftedPieceEquiv 𝓐 d n).finrank_eq, Module.finrank_pi_fintype]

lemma hasSum_shifted_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    (d : ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ (n-d)) : ℝ) * q^n)
      (q^d * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  have h := (hasSum_polynomial k σ hq.le hq1).mul_left (q^d)
  apply h.congr_fun
  intro n
  change (Module.finrank k (Graded.polynomialGrading k σ (n+d-d)) : ℝ) * q^(n+d) = _
  rw [add_sub_cancel_right, zpow_add₀ hq.ne']
  ring

/-- Convergent Hilbert series and its normalization for the actual shifted free module. -/
theorem hasSum_shiftedFree (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {ι : Type*} [Fintype ι] (d : ι → ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ =>
      (Module.finrank k (Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) : ℝ) * q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  have h := hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_shifted_polynomial k σ (d i) hq hq1)
  rw [← Finset.sum_mul] at h
  apply h.congr_fun
  intro n
  rw [shiftedPiece_finrank, Nat.cast_sum, Finset.sum_mul]


section FiniteModule
variable {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

lemma degreeMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) : Function.Surjective (degreeMap 𝓜 𝓝 f hf n) := by
  intro m
  obtain ⟨v,hv⟩ := hs m.val
  refine ⟨DirectSum.decompose 𝓜 v n, ?_⟩
  apply Subtype.ext
  change f (Graded.component 𝓜 n v) = m.val
  have h := Graded.map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero, hv] at h
  exact h.symm.trans (DirectSum.decompose_of_mem_same 𝓝 m.property)
end FiniteModule

section HomogeneousBasis
variable {σ : Type ua} [Fintype σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (Graded.polynomialGrading k σ) 𝓜]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι (MvPolynomial σ k) M)
  (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))

include hd

omit [Fintype σ] [IsScalarTower k (MvPolynomial σ k) M] [DirectSum.Decomposition 𝓜] in
lemma basis_equivFun_symm_graded (n : ℤ) (v : ι → MvPolynomial σ k)
    (hv : v ∈ Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) :
    b.equivFun.symm v ∈ 𝓜 n := by
  rw [b.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro i _
  simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)

lemma finrank_homogeneous_basis (n : ℤ) :
    Module.finrank k (𝓜 n) =
      ∑ i, Module.finrank k (Graded.polynomialGrading k σ (n-d i)) := by
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  let f := degreeMap (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜
    b.equivFun.symm.toLinearMap (basis_equivFun_symm_graded 𝓜 b d hd) n
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply b.equivFun.symm.injective
      exact congrArg Subtype.val h
    · exact degreeMap_surjective _ _ b.equivFun.symm.toLinearMap
        (basis_equivFun_symm_graded 𝓜 b d hd) b.equivFun.symm.surjective n
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  exact shiftedPiece_finrank _ d n

/-- The precise Hilbert normalization for a finite homogeneous basis, with the source's
convention that a generator in degree `d` contributes `q^d`. -/
theorem hasSum_homogeneous_basis {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (hasSum_shiftedFree k σ d hq hq1).congr_fun
  intro n
  rw [finrank_homogeneous_basis 𝓜 b d hd, shiftedPiece_finrank]
end HomogeneousBasis


end KLInvariance.Hilbert


end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

/-! Graded uniqueness/recognition for the genuinely constructed minimal
boundary covers. Character and self-duality are not included in this data. -/

namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem extend_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hBmin : B.KernelMinimal x) (hCmin : C.KernelMinimal x) :
    ∃ e : B.vertex x ≃ₗ[A] C.vertex x,
      (∀ n v, v ∈ (B.vertex x).piece n → e v ∈ (C.vertex x).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let g : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hgs : Function.Surjective g.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hfm : LinearMap.ker f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
    intro v hv
    apply (B.kernelMinimal_iff x).mp hBmin
    apply LinearMap.mem_ker.mpr
    apply j.boundary.injective
    rw [map_zero]
    have hh : f.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  have hgm : LinearMap.ker g.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : g.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let F : ModuleData.MinimalCover T := ⟨B.vertex x,hBfree,f,hfs,hfm⟩
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,g,hgs,hgm⟩
  obtain ⟨e,he,hef⟩ := ModuleData.MinimalCover.equiv hneg hzero F D
  refine ⟨e,he,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hef v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso

end


section

/-! Recognition of the actual finite minimal boundary sheaf. This proves
choice-independence of the constructed graded object, not its KL character. -/
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B C : BoundarySheaf hneg G α b) (hb : ∀ x, x ≤ b)

omit [Fintype V] in
include hzero hb in
 theorem extend_iso {U : Set V} (hU : IsUpperSet U)
    (j : GradedSheaf.OnIso B.sheaf C.sheaf U)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U) :
    Nonempty (GradedSheaf.OnIso B.sheaf C.sheaf (insert x U)) := by
  classical
  by_cases hxb : x=b
  · subst x
    let eqv := ModuleData.equivOfEq (B.top.trans C.top.symm)
    have heqv := ModuleData.equivOfEq_graded (B.top.trans C.top.symm)
    refine ⟨j.extend hU b hx hmax α B.quotient C.quotient eqv heqv ?_⟩
    intro e he
    exact False.elim ((not_lt_of_ge (hb (G.target e))) (he ▸ G.increasing e))
  · let ja := j.toOnIso.above x hmax
    obtain ⟨e,he,hcomm⟩ := ja.extend_stalk_graded hneg hzero
      (fun e ht => j.edge_graded e (hmax ht)) (B.free x) (C.free x)
      B.flabby.flabby B.generated C.flabby.flabby C.generated
      (B.minimal x hxb) (C.minimal x hxb)
    refine ⟨j.extend hU x hx hmax α B.quotient C.quotient e he ?_⟩
    intro f hf v
    subst x
    exact congrFun (hcomm v) ⟨f,rfl⟩

include hzero hb in
 theorem exists_gradedIso : Nonempty (GradedSheaf.Iso B.sheaf C.sheaf) := by
  classical
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      GradedSheaf.OnIso B.sheaf C.sheaf ((s : Set V)ᶜ) →
      Nonempty (GradedSheaf.Iso B.sheaf C.sheaf) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU j
      by_cases hs : s=∅
      · subst s
        have heq : ((∅ : Finset V) : Set V)ᶜ=Set.univ := by simp
        exact ⟨GradedSheaf.OnIso.ofUniv (heq ▸ j)⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        obtain ⟨jj⟩ := B.extend_iso hzero C hb hU j x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : GradedSheaf.OnIso B.sheaf C.sheaf (∅ : Set V) := by
    refine { toOnIso := ?_, vertex_graded := ?_, edge_graded := ?_ }
    · exact ⟨fun x hx => False.elim hx, fun e he => False.elim he,
        fun e hs => False.elim hs, fun e ht => False.elim ht⟩
    · intro x hx; exact False.elim hx
    · intro e he; exact False.elim he
  have hh := h Finset.univ
  rw [hset] at hh
  exact hh isUpperSet_empty hj

end KLInvariance.MomentGraph.BoundarySheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]

attribute [instance] NonnegativeBasis.finite

namespace NonnegativeBasis
variable {𝓜} (b : NonnegativeBasis (σ := σ) 𝓜)

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma eval₂_eq (q : ℝ) : Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial =
    ∑ i, q ^ b.degree i := by
  change (Polynomial.eval₂RingHom (Int.castRingHom ℝ) q) (∑ i, X ^ b.degree i) = _
  simp

omit [Finite σ] in
lemma hasSum [Fintype σ] {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial * (1-q)⁻¹ ^ Fintype.card σ) := by
  rw [b.eval₂_eq]
  convert Hilbert.hasSum_homogeneous_basis 𝓜 b.basis (fun i => (b.degree i : ℤ))
    b.homogeneous hq hq1 using 1
  all_goals try with_reducible_and_instances rfl
  simp

lemma polynomial_eq (c : NonnegativeBasis (σ := σ) 𝓜) : b.polynomial = c.polynomial := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {q | Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))} := by
    intro q hq
    have h := (b.hasSum hq.1 hq.2).unique (c.hasSum hq.1 hq.2)
    have hne : (1-q)⁻¹ ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq.2)))
    change Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))
    simpa only [Polynomial.eval_map] using mul_right_cancel₀ hne h
  exact Set.Infinite.mono hsub (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))

end NonnegativeBasis

lemma character_eq [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥)
    (b : NonnegativeBasis (σ := σ) 𝓜) : character (σ := σ) 𝓜 hneg = b.polynomial :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial_eq b

end KLInvariance.Graded

end


section

/-! Graded linear equivalence preserves the genuine free-module character.
This does not assert its identification with any KL polynomial. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ)}

 theorem character_eq_of_gradedEquiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N] (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n) :
    character (σ := σ) M.piece M.nonneg = character (σ := σ) N.piece N.nonneg := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [character_eq M.piece M.nonneg b,
    character_eq N.piece N.nonneg (mapNonnegativeBasis e he b)]
  rfl

end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottHeadKernelPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottHeadPairAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottHeadPairModule _root_.OAI.KLInvariance.TitsSpace.bottHeadRightKernelPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottPiece_graded _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree _root_.OAI.KLInvariance.TitsSpace.bottRealModule _root_.OAI.KLInvariance.TitsSpace.bottRealTower _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.bottStalkFinite _root_.OAI.KLInvariance.TitsSpace.bottStalkFree _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_decomposition _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_graded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_1
theorem lowerCharacter_zero (c x : Interval cs 1 b) (hx : ¬x ≤ c) :
    lowerCharacter cs b basis c x=0 := dite_eq_right hx

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Actual integral projection and support lattices inherit their grading from
the genuine tensor word. In particular a homogeneous stalk vector has a
homogeneous tensor lift. No freeness/character claim is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro h e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact h
  · intro h
    exact h ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

end
end KLInvariance.TitsSpace

end


section

/-! A homogeneous integral equivalence induces genuine shifted degreewise
vector-space equivalences, including its inverse grading. -/
namespace KLInvariance.Graded
universe uk um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]
  (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
  (e : M ≃ₗ[k] N) (d : ℤ)
  (he : ∀ n m, m ∈ 𝓜 n → e m ∈ 𝓝 (n+d))
noncomputable section

include e he in
 theorem finrank_homogeneousEquiv (n : ℤ) :
    Module.finrank k (𝓝 n)=Module.finrank k (𝓜 (n-d)) := by
  have h := (homogeneousPieceEquiv 𝓜 𝓝 e d he (n-d)).finrank_eq
  have hn : n-d+d=n := by omega
  rw [hn] at h
  exact h.symm

end
end KLInvariance.Graded

end


section

/-! The genuine Bott--Samelson stalk Hilbert coefficients satisfy the simple
reflection ascent recurrence. Both exactness and the degree-one kernel shift
were constructed integrally above; no KL character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance symmetricGrading_finite (n : ℤ) : Module.Finite ℝ (symmetricGrading basis n) :=
  inferInstanceAs (Module.Finite ℝ ((polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap))

 instance bottCoordinatePiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottCoordinatePiece cs basis l x n) := by
  classical
  exact piPiece_finite _ n

 instance bottStalkPiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottStalkPiece cs basis l x n) :=
  inferInstanceAs (Module.Finite ℝ (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x) n))

end
end KLInvariance.TitsSpace

end


section

/-! The genuine nonnegative polynomial generator character of word stalks,
with its convergent Hilbert-series interpretation. No KL identification is
asserted or included in the definition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPolynomialStalk_finrank (l : List I) (x : W) (n : ℤ) :
    Module.finrank ℝ ((bottPolynomialStalkData cs basis l x).piece n)=
      Module.finrank ℝ (bottStalkPiece cs basis l x n) :=
  LinearEquiv.finrank_map_eq
    (CoefficientChange.kEquiv (SymmetricAlgebra.equivMvPolynomial basis)
      (bottStalkData cs basis l x)) _

 theorem bottStalkCharacter_hasSum (l : List I) (x : W) {q : ℝ}
    (hq : 0<q) (hq1 : q<1) :
    HasSum (fun n : ℤ => (Module.finrank ℝ (bottStalkPiece cs basis l x n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q (bottStalkCharacter cs basis l x) *
        (1-q)⁻¹ ^ Fintype.card σ) := by
  have hh := (exists_nonnegativeBasis (k := ℝ) (σ := σ) (𝓜 := (bottPolynomialStalkData cs basis l x).piece)
    (bottPolynomialStalkData cs basis l x).nonneg).some.hasSum hq hq1
  apply hh.congr_fun
  intro n
  rw [bottPolynomialStalk_finrank]

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/

section

namespace KLInvariance.Hilbert
open Polynomial

 theorem numerator_unique (f : ℤ → ℕ) (F G : ℤ[X]) (D : ℝ → ℝ)
    (hD : ∀ q, 0<q → q<1 → D q≠0)
    (hF : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q F*D q))
    (hG : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q G*D q)) : F=G := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_ (Set.Ioo_infinite (by norm_num))
  intro q hq
  have he := (hF q hq.1 hq.2).unique (hG q hq.1 hq.2)
  change eval q (F.map (Int.castRingHom ℝ))=eval q (G.map (Int.castRingHom ℝ))
  simpa only [eval_map] using (mul_right_cancel₀ (hD q hq.1 hq.2) he)

end KLInvariance.Hilbert

end


section

/-! Genuine word stalk normalization and identification with the honest
Hecke word. This does not identify the indecomposable BMP character with KL. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_7
omit [Fintype σ] in
 theorem bottTopPolynomialEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) (hs : s∈bottStalkPiece cs basis l (cs.wordProd l) n) :
    bottTopPolynomialEquiv cs basis l hl s∈polynomialGrading ℝ σ n := by
  apply (mem_symmetricGrading basis n _).mp
  exact (bottTopStalkEquiv_homogeneous cs basis l hl n s).mpr hs

 theorem bottStalkCharacter_top (l : List I) (hl : cs.IsReduced l) :
    bottStalkCharacter cs basis l (cs.wordProd l)=1 := by
  have hd (n : ℤ) : Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)=
      Module.finrank ℝ (polynomialGrading ℝ σ n) := by
    have hh := finrank_homogeneousEquiv (bottStalkPiece cs basis l (cs.wordProd l))
      (polynomialGrading ℝ σ) (bottTopPolynomialEquiv cs basis l hl) 0
      (fun n s hs => by simpa only [add_zero] using bottTopPolynomialEquiv_homogeneous cs basis l hl n s hs) n
    have hz : n-(0:ℤ)=n := Int.sub_zero n
    rw [hz] at hh
    exact hh.symm
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.wordProd l)
  · intro q hq hq1
    simpa only [hd,Polynomial.eval₂_one,one_mul] using Hilbert.hasSum_polynomial ℝ σ hq.le hq1

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section


namespace KLInvariance.MomentGraph.GradedSheaf
open Module _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E] [DecidableEq V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)
  [IsNoetherianRing A] [IsDomain A]
  [∀ x, Module.IsTorsionFree A (B.forget.vertex x)]
  (α : E → A) (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (p : B.forget.sections Set.univ ≃ₗ[A] Dual A (B.forget.sections Set.univ))
  (hbalanced : ∀ x m n,
    p (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x m) n =
    p m (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x n))
noncomputable section

 theorem dualToSupport_homogeneous (l : ℤ)
    (hp : ∀ i j (m n : B.sections Set.univ),
      m ∈ (B.sections Set.univ).piece i → n ∈ (B.sections Set.univ).piece j →
      p m n ∈ 𝓐 (i+j-l))
    (x : V) (r : ℤ) (lam : Dual A (B.vertex x))
    (hlam : ∀ j (v : B.vertex x), v ∈ (B.vertex x).piece j → lam v ∈ 𝓐 (j+r)) :
    (IntegralSupport.dualToSupport (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha))
      (Sheaf.labelProduct_ne_zero α hα) p hbalanced x lam).val ∈
        (B.sections Set.univ).piece (r+l) := by
  apply perfect_inverse_of_homogeneous_functional 𝓐 (B.sections Set.univ).piece p l hp r
  intro j n hn
  exact hlam j (n.val x) (hn x (Set.mem_univ x))

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]

/-- Cancellation of an injective homogeneous scalar action includes the
inverse grading shift. It does not require the scalar to be a unit. -/
 theorem mem_of_homogeneous_smul (d : ℤ) (a : A) (ha : a ∈ 𝓐 d)
    (hinj : Function.Injective (fun m : M => a • m))
    (n : ℤ) (m : M) (hm : a • m ∈ 𝓜 n) : m ∈ 𝓜 (n-d) := by
  have hc : component 𝓜 (n-d) m = m := by
    apply hinj
    change a • component 𝓜 (n-d) m = a • m
    rw [← component_homogeneous_smul 𝓐 𝓜 d a ha]
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  rw [← hc]
  exact (DirectSum.decompose 𝓜 m (n-d)).property

end KLInvariance.Graded

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

omit [Fintype (Interval cs u b)] in
 theorem incomingProduct_homogeneous (x : Interval cs u b) :
    Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x ∈
      polynomialGrading ℝ σ ((Sheaf.incoming (G := graph cs u b) x).card : ℤ) := by
  simpa only [Sheaf.incomingProduct,Finset.sum_const,Int.natCast_one,mul_one,nsmul_eq_mul] using
    SetLike.prod_mem_graded (polynomialGrading ℝ σ) (fun _ : Edge cs u b => (1 : ℤ))
      (polynomialLabel cs u b basis)
      (F := Sheaf.incoming (G := graph cs u b) x)
      (fun e _ => polynomialLabel_homogeneous cs u b basis e)

end
end KLInvariance.BruhatGraph

end


section

/-! The degree of the actual incoming root product on [1,b].  This is not
asserted for truncated intervals with arbitrary bottom. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
noncomputable section

 theorem incoming_card [Fintype (Edge cs 1 b)] [DecidableEq (Interval cs 1 b)]
    (x : Interval cs 1 b) : (Sheaf.incoming (G := graph cs 1 b) x).card = cs.length x.val := by
  classical
  calc
    _ = Nat.card {e : Edge cs 1 b // target cs 1 b e = x} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    _ = Nat.card {t : W // cs.IsLeftInversion x.val t} := Nat.card_congr (incomingEquivInversions cs b x)
    _ = Nat.card (RootInversions M cs x.val) := Nat.card_congr (rootInversionEquiv M cs x.val).symm
    _ = cs.length x.val := card_rootInversions M cs x.val

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Integral costalk duality only uses free stalks, the genuine edge quotients,
generation and a perfect support-orthogonal section form. No top/minimality or
KL character assumption is needed. This extension applies to genuine words. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))

namespace FreeSheaf
variable (B : FreeSheaf cs u b basis)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 variable [Fintype σ] [Fintype (Interval cs u b)]

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis B d x).symm lam).val ∈
      (B.sheaf.vertex x).piece
        (r+l-(Sheaf.incoming (G := graph cs u b) x).card) := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  let S := B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
    (polynomialLabel_ne_zero cs u b basis)
    (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
    d.pairing d.balanced B.generated x
  have hs : (S.symm lam).val ∈ (B.sheaf.sections Set.univ).piece (r+l) := by
    exact B.sheaf.dualToSupport_homogeneous (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced l hd x r lam hlam
  have hv := hs x (Set.mem_univ x)
  have he : (S.symm lam).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x •
      ((costalkEquivDual cs u b basis B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis B x)
        ((kernelEquivSingleSupport cs u b basis B x).symm (S.symm lam))).val.val x
    rw [LinearEquiv.apply_symm_apply]
  change (S.symm lam).val.val x ∈ (B.sheaf.vertex x).piece (r+l) at hv
  rw [he] at hv
  apply mem_of_homogeneous_smul (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
    ((Sheaf.incoming (G := graph cs u b) x).card : ℤ)
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x)
    (incomingProduct_homogeneous cs u b basis x) _ (r+l) _ hv
  let _ := B.free x
  exact smul_right_injective _ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)

end
end FreeSheaf
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph.FreeSheaf
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (B : FreeSheaf cs 1 b basis)
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 theorem kernelDual_homogeneous (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (x : Interval cs 1 b) (hn : cs.length x.val≤n) (r : ℤ)
    (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v∈(B.sheaf.vertex x).piece j →
      lam v∈polynomialGrading ℝ σ (j+r)) :
    kernelDual cs b basis B d x lam∈(GradedSheaf.kernelData B.sheaf x).piece
      (r+(n-cs.length x.val : ℕ)) := by
  have h := costalkEquivDual_inverse_homogeneous cs 1 b basis B d n hd x r lam hlam
  rw [incoming_card] at h
  change ((costalkEquivDual cs 1 b basis B d x).symm lam).val∈
    (B.sheaf.vertex x).piece (r+↑(n-cs.length x.val))
  have he : r+(n:ℤ)-cs.length x.val=r+↑(n-cs.length x.val) := by omega
  rwa [he] at h

end
end KLInvariance.BruhatGraph.FreeSheaf

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteInterval
attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteEdges
attribute [local instance] OAI.KLInvariance.BruhatGraph.charDecEqC
theorem stalkBasis_degree_le (x : Interval cs 1 b)
    (c : NonnegativeBasis (σ := σ)
      ((boundaryFreeSheaf cs b basis).sheaf.vertex x).piece) (i : c.index) :
    c.degree i ≤ rankDifference cs x.val b := by
  apply ModuleData.degree_le_of_dual_equiv _ _
    (FreeSheaf.kernelDual cs b basis _ (boundaryFreeDuality cs b basis) x)
    (rankDifference cs x.val b) _ c i
  exact FreeSheaf.kernelDual_homogeneous cs b basis _ (boundaryFreeDuality cs b basis)
    (cs.length b) (fun i j m a hm ha => (boundaryPerfectPairing cs b basis).homogeneous i j m a
      (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x)))
    x (length_le_of_bruhat cs x.property.2)

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
noncomputable section

 theorem char_unit :
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).char=1 := by
  rw [char,character_eq _ _ (unitPolynomialBasis (k := k) (σ := σ))]
  change (∑ i : PUnit.{max uk us um + 1}, (X : Polynomial ℤ)^0)=1
  simp

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_3
theorem stalkCharacter_top :
    stalkCharacter cs 1 b basis (one_bruhat cs b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=1 := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
  change (B.sheaf.vertex ⟨b,one_bruhat cs b,bruhat_refl cs b⟩).char=1
  exact (ModuleData.character_eq_of_gradedEquiv (ModuleData.equivOfEq B.top)
    (ModuleData.equivOfEq_graded B.top)).trans ModuleData.char_unit

 theorem lowerCharacter_diagonal (c : Interval cs 1 b) : lowerCharacter cs b basis c c=1 := by
  rw [lowerCharacter,dite_eq_left le_rfl]
  exact stalkCharacter_top cs c.val basis

 theorem lowerCharacter_at_top (c : Interval cs 1 b) :
    lowerCharacter cs b basis c ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=
      if c.val=b then 1 else 0 := by
  by_cases hc : c.val=b
  · have he : c=⟨b,one_bruhat cs b,bruhat_refl cs b⟩ := Subtype.ext hc
    rw [ite_eq_left hc,←he,lowerCharacter_diagonal]
  · rw [ite_eq_right hc]
    apply lowerCharacter_zero
    intro h
    exact hc (bruhat_antisymm cs c.property.2 h)

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.BruhatGraph.lowerConvInterval
theorem lowerCharacter_convolution (c x : Interval cs 1 b) :
    (∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z)=
      ∑ z : Interval cs 1 c.val, OrdinaryR.polynomial cs x.val z.val*
        stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z := by
  classical
  let f (z : Interval cs 1 b) := OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z
  have hf : ∀ z : Interval cs 1 b, ¬z ≤ c → f z=0 := by
    intro z hz
    simp only [f,lowerCharacter_zero cs b basis c z hz,mul_zero]
  have he : (∑ z : Interval cs 1 b, f z) = ∑ z ∈ Finset.univ.filter (fun z => z ≤ c), f z := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z _ hz
    exact hf z (by simpa using hz)
  change (∑ z, f z)=_
  rw [he,Finset.sum_subtype (p := fun z : Interval cs 1 b => z ≤ c) _ (by simp)]
  calc
    _ = ∑ z : Set.Iic c, OrdinaryR.polynomial cs x.val z.val.val*
        stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) ((lowerIntervalEquiv cs b c) z) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [f,lowerCharacter,dite_eq_left z.property]
      rfl
    _ = _ := Equiv.sum_comp (lowerIntervalEquiv cs b c) (fun z => OrdinaryR.polynomial cs x.val z.val*
      stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z)

 theorem lowerCharacter_convolution_zero (c x : Interval cs 1 b) (hx : ¬x ≤ c) :
    (∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z)=0 := by
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z ≤ c
  · rw [OrdinaryR.polynomial_zero cs x.val z.val (fun h => hx (bruhat_trans cs h hz)),zero_mul]
  · rw [lowerCharacter_zero cs b basis c z hz,mul_zero]

 theorem lowerCharacter_reciprocity_lift (c : Interval cs 1 b)
    (h : ∀ x : Interval cs 1 c.val,
      reflect (rankDifference cs x.val c.val) (stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) x)=
        ∑ z : Interval cs 1 c.val, OrdinaryR.polynomial cs x.val z.val*
          stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z)
    (x : Interval cs 1 b) :
      reflect (rankDifference cs x.val c.val) (lowerCharacter cs b basis c x)=
        ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z := by
  by_cases hx : x ≤ c
  · rw [lowerCharacter_convolution,lowerCharacter,dite_eq_left hx]
    exact h ⟨x.val,x.property.1,hx⟩
  · rw [lowerCharacter_zero cs b basis c x hx,reflect_zero,lowerCharacter_convolution_zero cs b basis c x hx]

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/

section

namespace KLInvariance
universe u v
variable {V : Type u} [Fintype V] {C : Type v} [CommRing C]

 theorem finite_character_cancellation (t : V) (m : V → C) (r : V → C)
    (p : V → V → C) (q : V → C) (hm : m t=1)
    (hword : (∑ y, m y*q y)=∑ z, r z*(∑ y, m y*p y z))
    (hlower : ∀ y, y≠t → q y=∑ z, r z*p y z) : q t=∑ z, r z*p t z := by
  classical
  have hexpand : (∑ z, r z*(∑ y, m y*p y z))=∑ y, m y*(∑ z, r z*p y z) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hexpand] at hword
  have hzero : (∑ y, m y*(q y-∑ z, r z*p y z))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,hword,sub_self]
  have hsingle : (∑ y, m y*(q y-∑ z, r z*p y z))=q t-∑ z, r z*p t z := by
    rw [Finset.sum_eq_single t]
    · rw [hm,one_mul]
    · intro y _ hy
      rw [hlower y hy,sub_self,mul_zero]
    · simp
  rw [hsingle] at hzero
  exact sub_eq_zero.mp hzero

end KLInvariance

end


section

/-! R-reciprocity for the ACTUAL minimal-boundary BMP character, obtained
by simultaneous word stalk/costalk decomposition and unipotent cancellation.
This is not a character identification: strict halfdegree remains separate. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 local instance instDecidable_solutions_5_rac141c_1 (p : Prop) : Decidable p := Classical.propDecidable p
attribute [local instance] OAI.KLInvariance.BruhatGraph.bmpRecInterval
theorem stalkCharacter_reciprocity (b : W) (x : Interval cs 1 b) :
    reflect (rankDifference cs x.val b) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)=
      ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*
        stalkCharacter cs 1 b basis (one_bruhat cs b) z := by
  generalize hn : cs.length b=n
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    obtain ⟨l,hl,rfl⟩ := cs.exists_isReduced b
    let b := cs.wordProd l
    let t : Interval cs 1 b := ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
    obtain ⟨m,_hm,hs,hk⟩ := bottCharacter_decomposition_both cs basis l hl
    have hmt : m t=1 := by
      have hh := hs t
      rw [bottStalkCharacter_top cs basis l hl] at hh
      rw [Finset.sum_eq_single t] at hh
      · simpa only [lowerCharacter_diagonal,mul_one] using hh.symm
      · intro y _ hy
        have hv : y.val≠b := fun h => hy (Subtype.ext h)
        rw [lowerCharacter_at_top,ite_eq_right hv,mul_zero]
      · simp
    have ht (z : Interval cs 1 b) : lowerCharacter cs b basis t z=
        stalkCharacter cs 1 b basis (one_bruhat cs b) z := dite_eq_left z.property.2
    have hw : (∑ y, m y*reflect (rankDifference cs x.val y.val) (lowerCharacter cs b basis y x))=
        ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*
          (∑ y, m y*lowerCharacter cs b basis y z) := by
      rw [←hk x,bottKernelCharacter_rConvolution cs basis l hl x]
      simp only [hs]
      rfl
    have hh := finite_character_cancellation t m
      (fun z : Interval cs 1 b => OrdinaryR.polynomial cs x.val z.val)
      (fun y z => lowerCharacter cs b basis y z)
      (fun y => reflect (rankDifference cs x.val y.val) (lowerCharacter cs b basis y x))
      hmt hw (fun y hy => ?_)
    · simpa only [ht] using hh
    · apply lowerCharacter_reciprocity_lift
      intro z
      apply ih (cs.length y.val) _ y.val z rfl
      rw [←hn]
      exact length_lt_of_bruhat_ne cs y.property.2 (fun he => hy (Subtype.ext he))

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (C : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 theorem boundarySheaf_gradedIso :
    Nonempty (GradedSheaf.Iso (boundarySheaf cs u b basis hub).sheaf C.sheaf) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  let : Fintype (Edge cs u b) := Fintype.ofFinite _
  exact BoundarySheaf.exists_gradedIso (polynomialGrading_zero ℝ σ)
    (boundarySheaf cs u b basis hub) C (fun x => x.property.2)

 theorem stalkCharacter_eq_character (x : Interval cs u b) :
    let _ := C.free x
    stalkCharacter cs u b basis hub x =
      Graded.character (σ := σ) (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg := by
  let _ := C.free x
  let B := boundarySheaf cs u b basis hub
  let _ := B.free x
  obtain ⟨j⟩ := boundarySheaf_gradedIso cs u b basis hub C
  exact ModuleData.character_eq_of_gradedEquiv (j.vertex x) (j.vertex_graded x)

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.scaledInterval
theorem stalkCharacter_natDegree_le (x : Interval cs 1 b) :
    (stalkCharacter cs 1 b basis (one_bruhat cs b) x).natDegree ≤ rankDifference cs x.val b := by
  classical
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free x
  let c := (exists_nonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg).some
  rw [stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) B x,
    character_eq (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg c]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  simpa only [Polynomial.natDegree_X_pow] using stalkBasis_degree_le cs b basis x c i

 theorem scaledStalk_reciprocity_inverse {C : Type*} [Field C]
    (v : C) (hv : v≠0) (x : Interval cs 1 b) :
    scaledStalk cs b basis v⁻¹ x=∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis v z := by
  classical
  have hrec := stalkCharacter_reciprocity cs basis b x
  let q : Cˣ := Units.mk0 (v^2) (pow_ne_zero 2 hv)
  have heval := congrArg (eval₂ (Int.castRingHom C) (q : C)) hrec
  rw [eval₂_reflect_unit q _ _ (stalkCharacter_natDegree_le cs b basis x)] at heval
  simp only [eval₂_finsetSum,eval₂_mul] at heval
  have hq : (q : C)=v^2 := rfl
  have hqi : (↑q⁻¹ : C)=(v⁻¹)^2 := by simp [q,inv_pow]
  rw [hq,hqi] at heval
  have heq := congrArg (fun a : C => v^((cs.length x.val : ℤ)-cs.length b)*a) heval
  have hd : (rankDifference cs x.val b : ℤ)=(cs.length b : ℤ)-cs.length x.val := by
    simp [rankDifference,Int.ofNat_sub (length_le_of_bruhat cs x.property.2)]
  have hscale : v^((cs.length x.val : ℤ)-cs.length b)*(v^2)^(rankDifference cs x.val b)=
      (v⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [←pow_mul,←zpow_natCast,←zpow_add₀ hv,inv_zpow,←zpow_neg]
    congr 1
    push_cast
    omega
  rw [←mul_assoc,hscale,Finset.mul_sum] at heq
  change (v⁻¹)^((cs.length x.val : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) ((v⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)=_
  rw [heq]
  apply Finset.sum_congr rfl
  intro z _
  have hr : OrdinaryR.polynomial cs x.val z.val=rPolynomial cs x.val z.val :=
    (rPolynomial_eq_constructed cs x.val z.val).symm
  rw [hr,rPolynomial_normalization cs v hv]
  unfold scaledStalk
  calc
    _ = (v^((cs.length x.val : ℤ)-cs.length b)*v^((cs.length z.val : ℤ)-cs.length x.val))*
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val)*
        eval₂ (Int.castRingHom C) (v^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) z) := by ring
    _ = _ := by
      rw [←zpow_add₀ hv,show (cs.length x.val : ℤ)-cs.length b+
        ((cs.length z.val : ℤ)-cs.length x.val)=(cs.length z.val : ℤ)-cs.length b by ring]
      ring

 theorem scaledStalk_reciprocity {C : Type*} [Field C]
    (t : C) (ht : t≠0) (x : Interval cs 1 b) :
    scaledStalk cs b basis t x=∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis t⁻¹ z := by
  simpa only [inv_inv] using scaledStalk_reciprocity_inverse cs b basis t⁻¹ (inv_ne_zero ht) x

 theorem scaledStalk_reciprocity_upper_oai {C : Type*} [Field C]
    (t : C) (ht : t≠0) (a : W) (x : Interval cs a b) :
    scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)=
      ∑ᶠ z : Interval cs a b,
        eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
          scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z) := by
  classical
  let := interval_finite cs a b
  let := Fintype.ofFinite (Interval cs a b)
  rw [scaledStalk_reciprocity cs b basis t ht, finsum_eq_sum_of_fintype]
  let e : {z : Interval cs 1 b // BruhatLE cs a z.val} ≃ Interval cs a b :=
    ⟨fun z => ⟨z.val.val,z.property,z.val.property.2⟩,
      fun z => ⟨(upperInclusion cs a b).vertex z,z.property.1⟩,fun _ => rfl,fun _ => rfl⟩
  let g (z : Interval cs 1 b) :=
    eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*scaledStalk cs b basis t⁻¹ z
  change (∑ z : Interval cs 1 b, g z)=_
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : Interval cs 1 b => BruhatLE cs a z.val),g z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z _ hz
      have hnot : ¬BruhatLE cs x.val z.val := by
        intro hxz
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bruhat_trans cs x.property.1 hxz⟩)
      simp [g,Hecke.rTilde_zero cs x.val z.val hnot]
    _ = ∑ z : {z : Interval cs 1 b // BruhatLE cs a z.val}, g z.val :=
      Finset.sum_subtype _ (by simp) g
    _ = _ := Equiv.sum_comp e (fun z =>
      eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z))

end
end KLInvariance.BruhatGraph

end


end OAI
end

theorem solution.{u, u_1} : type_of% @OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper_oai.{u, u_1} := @OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper_oai.{u, u_1}
