-- Prove2me | solution 1 for OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:36:10.911615+00:00
-- url     : https://prove2.me/submissions/77839fad-1bd9-443e-8c1c-1ade75b4f2e7

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K024
import Theorems.Thm_OAI_KLInvariance_BruhatGraph_scaledStalk_reciprocity_upper

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

namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

attribute [local instance] OAI.KLInvariance.Dihedral.instDecidable_solutions
theorem eq_alt_of_descent (cs : CoxeterSystem M W) (i : Bool) {w : W}
    (h : cs.length (cs.simple i * w) < cs.length w) :
    w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced (cs.simple i * w)
  have hlen : cs.length w = ω.length + 1 := by
    have := cs.length_simple_mul w i
    rw [hw, hω.eq] at this h
    omega
  have hp : cs.wordProd (i :: ω) = w := by
    simp only [cs.wordProd_cons, ← hw, cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: ω) := by
    simpa only [CoxeterSystem.IsReduced, hp, List.length_cons] using hlen
  rw [hlen, ← reduced_cons_eq_alt cs i ω hr, hp]

end KLInvariance.Dihedral

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section


namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
variable (source target : E → V)

variable [Semiring R]

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions
/-- The full matrix expansion, each sublist contributing exactly one path
term. Noncomposable sublists contribute zero by the definition of pathTerm. -/
theorem dispatch_eq_path_sum (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ((p.sublists').map (fun q => pathTerm source target T v q x)).sum := by
  classical
  induction p generalizing x with
  | nil => simp [dispatch, List.sublists', pathTerm]
  | cons e p ih =>
    rw [dispatch,step,List.sublists'_cons,List.map_append,List.sum_append,List.map_map]
    rw [ih x]
    congr 1
    by_cases he : source e = x
    · simp only [Function.comp_def,pathTerm,he,ite_true, if_true]
      rw [List.sum_map_mul_left,ih (target e)]
    · simp [Function.comp_def,he,pathTerm]

/-- With a delta initial value, a path contributes its length weight, not an
invariant defined by the desired conclusion. -/
theorem pathTerm_delta (T : R) (x y : V) (p : List E) :
    pathTerm source target T (fun z => if z = y then 1 else 0) p x =
      if IsPath source target x y p then T ^ p.length else 0 := by
  classical
  induction p generalizing x with
  | nil => simp [pathTerm,IsPath]
  | cons e p ih =>
    simp only [pathTerm,IsPath,List.length_cons]
    by_cases he : source e = x
    · rw [ite_eq_left he,ih]
      by_cases hp : IsPath source target (target e) y p
      · simp only [hp,he,and_self,ite_true, if_true,pow_succ']
      · simp [hp,he]
    · simp [he]

/-- The entry of the elementary-matrix product is exactly the sum of weights
of directed schedule-subpaths. -/
theorem entry_eq_weighted_paths (T : R) (p : List E) (x y : V) :
    dispatch source target T (fun z => if z = y then 1 else 0) p x =
      ((p.sublists').map (fun q =>
        if IsPath source target x y q then T ^ q.length else 0)).sum := by
  classical
  rw [dispatch_eq_path_sum]
  congr 1
  exact List.map_congr_left (fun q _ => pathTerm_delta source target T x y q)


section LabelOrder
variable {Λ : Type*} [LinearOrder Λ] (label : E → Λ)

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions
/-- Ties in a legitimate reflection schedule cannot occur on a composable
pair. Hence every nonzero term in the schedule expansion has strictly
rather than merely weakly decreasing labels. -/
theorem decreasing_of_schedule_path
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    {p : List E} {x y : V}
    (hp : IsPath source target x y p)
    (hs : p.Pairwise (fun e f => label f ≤ label e)) :
    p.Pairwise (fun e f => label f < label e) := by
  induction p generalizing x with
  | nil => exact List.Pairwise.nil
  | cons e p ih =>
    cases p with
    | nil => simp
    | cons f p =>
      have ht : IsPath source target (target e) y (f :: p) := hp.2
      have hef : label f < label e := by
        apply lt_of_le_of_ne ((List.pairwise_cons.mp hs).1 f (List.mem_cons_self))
        intro heq
        exact hties e f heq.symm ht.1.symm
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih ht hs.tail⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hef
      · exact lt_of_le_of_lt ((List.pairwise_cons.mp hs.tail).1 g hg) hef

/-- Every strictly decreasing edge list contained in a weakly decreasing
schedule occurs as a sublist. This also handles arbitrary ordering of ties:
a strict list can use at most one edge of each label. -/
theorem sublist_of_decreasing_subset {p schedule : List E}
    (hp : p.Pairwise (fun e f => label f < label e))
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hmem : p ⊆ schedule) : List.Sublist p schedule := by
  induction schedule generalizing p with
  | nil =>
    have : p = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => List.not_mem_nil (hmem ha))
    subst p
    exact List.Sublist.refl []
  | cons e schedule ih =>
    cases p with
    | nil => exact List.nil_sublist _
    | cons f p =>
      by_cases hef : e = f
      · subst f
        apply List.Sublist.cons_cons
        apply ih hp.tail hs.tail
        intro g hg
        rcases List.mem_cons.mp (hmem (List.mem_cons_of_mem e hg)) with heq | hin
        · have hlt := (List.pairwise_cons.mp hp).1 g hg
          rw [heq] at hlt
          exact (lt_irrefl _ hlt).elim
        · exact hin
      · apply List.Sublist.cons
        apply ih hp hs.tail
        intro g hg
        have hfg : f ∈ schedule := (List.mem_cons.mp (hmem (List.mem_cons_self))).resolve_left
          (Ne.symm hef)
        have hfe : label f ≤ label e := (List.pairwise_cons.mp hs).1 f hfg
        rcases List.mem_cons.mp (hmem hg) with heq | hin
        · subst g
          rcases List.mem_cons.mp hg with h | h
          · exact (hef h).elim
          · exact (not_lt_of_ge hfe ((List.pairwise_cons.mp hp).1 e h)).elim
        · exact hin

end LabelOrder

end
end KLInvariance.SchedulePaths

/-! NEW GRAPH CLOSURE -/


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.piPiece_finite _root_.OAI.KLInvariance.Graded.subPiece_finite _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottHeadPairAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup
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

lemma term_top {M : Type um} [AddCommGroup M] [Module k M]
    (𝓜 : ℤ → Submodule k M) (q : ℝ) (n : ℤ) :
    term 𝓜 ⊤ q n = (Module.finrank k (𝓜 n) : ℝ)*q^n := by
  rw [term, piece, Submodule.comap_top, finrank_top]

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


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 theorem term_subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (q : ℝ) (n : ℤ) :
    term (subPiece 𝓜 S) ⊤ q n = term 𝓜 (S.restrictScalars k) q n := by
  rw [term_top,term,(subPieceEquiv 𝓜 S n).finrank_eq]

 theorem value_subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (q : ℝ) :
    value (subPiece 𝓜 S) ⊤ q = value 𝓜 (S.restrictScalars k) q := by
  exact tsum_congr (term_subPiece 𝓜 S q)

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
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem simpleRoot_mem (i : Bool) : (B.simpleRoot i).val ∈ P := by
  cases i
  · exact B.left_mem
  · exact B.right_mem

end PlaneBasis


end
end KLInvariance.TitsSpace

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

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis hub B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis hub B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis hub B d x).symm lam).val ∈
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
      ((costalkEquivDual cs u b basis hub B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis hub B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis hub B x)
        ((kernelEquivSingleSupport cs u b basis hub B x).symm (S.symm lam))).val.val x
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

 theorem costalk_hilbert_of_duality
    (d : SectionDuality cs u b basis hub B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (c : NonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Hilbert.value (B.sheaf.vertex x).piece
      ((fullSubmodule cs u b basis hub B x).restrictScalars ℝ) q =
      q^(l-(Sheaf.incoming (G := graph cs u b) x).card) *
        Polynomial.eval₂ (Int.castRingHom ℝ) q⁻¹ c.polynomial *
        (1-q)⁻¹ ^ Fintype.card σ := by
  classical
  let K := fullKernel cs u b basis hub B x
  let cb : Basis c.index (Coefficient (σ := σ)) K :=
    c.basis.dualBasis.map (costalkEquivDual cs u b basis hub B d x).symm
  have hcb (i : c.index) : cb i ∈ K.piece
      (l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) := by
    change ((costalkEquivDual cs u b basis hub B d x).symm (c.basis.dualBasis i)).val ∈
      (B.sheaf.vertex x).piece _
    have h := costalkEquivDual_inverse_homogeneous cs u b basis hub B d l hd x
      (-(c.degree i : ℤ)) (c.basis.dualBasis i)
      (dualBasis_homogeneous (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
        c.basis (fun i => (c.degree i : ℤ)) c.homogeneous i)
    simpa only [show -(c.degree i : ℤ)+l-(Sheaf.incoming (G := graph cs u b) x).card =
      l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ) by omega] using h
  have hs := Hilbert.hasSum_homogeneous_basis K.piece cb
    (fun i => l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) hcb hq hq1
  have hv : Hilbert.value K.piece ⊤ q =
      (∑ i, q^(l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ))) *
        (1-q)⁻¹ ^ Fintype.card σ := by
    simpa only [Hilbert.value,Hilbert.term_top] using hs.tsum_eq
  change Hilbert.value (B.sheaf.vertex x).piece
    ((fullSubmodule cs u b basis hub B x).restrictScalars ℝ) q = _
  rw [← Hilbert.value_subPiece]
  change Hilbert.value K.piece ⊤ q = _
  rw [hv,c.eval₂_eq,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hq.ne',zpow_natCast,div_eq_mul_inv,inv_pow]

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem mem_coset_of_graphRoot {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : (graphRoot h).val ∈ P) : y*a₀⁻¹ ∈ planeSubgroup M cs P := by
  have hm := (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mpr hy
  convert (planeSubgroup M cs P).mul_mem hm hx using 1
  all_goals try with_reducible_and_instances rfl
  group

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem inverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : rootInverted w a) (hb : rootInverted w b) :
    rootInverted w c := by
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (ha i))
    (mul_nonpos_of_nonneg_of_nonpos hs (hb i))

/-- Incoming graph labels are actual inversions at their upper vertex. -/
theorem graphRoot_inverted_target {x y : W} (h : BruhatStep cs x y) :
    rootInverted y (graphRoot h) := by
  apply ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 y).mpr
  refine ⟨h.label_reflection, ?_⟩
  have he : (y*x⁻¹)*y=x := by
    calc
      (y*x⁻¹)*y = (y*x⁻¹)*((y*x⁻¹)*x) := by group
      _ = x := by rw [← mul_assoc,h.label_reflection.mul_self,one_mul]
  simpa only [he] using h.1

/-- Outgoing graph labels are actual noninversions at their lower vertex. -/
theorem graphRoot_not_inverted_source {x y : W} (h : BruhatStep cs x y) :
    ¬ rootInverted x (graphRoot h) := by
  intro hi
  have hh := ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 x).mp hi
  have he : (y*x⁻¹)*x=y := by group
  have hh' := hh.2
  rw [he] at hh'
  exact lt_asymm h.1 hh'

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- In a plane with its first simple root inverted, every noninverted root
is later than every inverted root. This uses convexity, not a signed-index
formula for a particular realization. -/
theorem slope_lt_of_inverted_left (w : W) (hl : rootInverted w B.left)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b := by
  by_contra h
  have hba : geometricSlope b < geometricSlope a :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hlb : geometricSlope B.left < geometricSlope b :=
    lt_of_le_of_ne (B.left_min b hbP) (fun he => hb (geometricSlope_injective he ▸ hl))
  have heq : rootPlane B.left a = P :=
    rootPlane_eq_of_mem B.left B.right B.left a B.distinct
      (Submodule.subset_span (Set.mem_insert _ _))
      (B.plane_eq.ge haP) (fun he => by rw [he] at hlb; exact (lt_asymm hlb hba)) |>.trans B.plane_eq
  obtain ⟨r,s,hr,hs,hc⟩ := positive_combination_of_slope_between B.left a b
    (heq.symm ▸ hbP) hlb hba
  exact hb (inverted_of_positive_combination w B.left a b hr.le hs.le hc hl ha)

/-- The other angular cut, when the last simple root is inverted. -/
theorem slope_lt_of_inverted_right (w : W) (hr : rootInverted w B.right)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope b < geometricSlope a := by
  by_contra h
  have hab : geometricSlope a < geometricSlope b :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hbr : geometricSlope b < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max b hbP) (fun he => hb (geometricSlope_injective he ▸ hr))
  have har : a ≠ B.right := by
    intro he
    rw [he] at hab
    exact lt_asymm hbr hab
  have heq : rootPlane a B.right = P :=
    (rootPlane_eq_of_mem B.left B.right a B.right B.distinct
      (B.plane_eq.ge haP) (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      har).trans B.plane_eq
  obtain ⟨r,s,hrr,hss,hc⟩ := positive_combination_of_slope_between a B.right b
    (heq.symm ▸ hbP) hab hbr
  exact hb (inverted_of_positive_combination w a B.right b hrr.le hss.le hc ha hr)

/-- In the mixed-sign case the angular cut is determined by the first
canonical simple root. In particular the comparison of consecutive path
labels depends only on their middle vertex. -/
theorem slope_lt_iff_inverted_left (w : W)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b ↔ rootInverted w B.left := by
  constructor
  · intro hab
    by_contra hl
    have hr : rootInverted w B.right := by
      by_contra hr
      obtain ⟨r,s,hrr,hss,he⟩ := B.positive_cone a haP
      exact noninverted_of_positive_combination w B.left B.right a hrr hss he hl hr ha
    exact lt_asymm hab (B.slope_lt_of_inverted_right w hr a b haP hbP ha hb)
  · intro hl
    exact B.slope_lt_of_inverted_left w hl a b haP hbP ha hb

/-- The exact middle-vertex test for two ascending graph arrows with both
labels in this root plane. -/
theorem consecutive_slopes_iff {x y z : W}
    (hxy : BruhatStep cs x y) (hyz : BruhatStep cs y z)
    (ha : (graphRoot hxy).val ∈ P) (hb : (graphRoot hyz).val ∈ P) :
    geometricSlope (graphRoot hxy) < geometricSlope (graphRoot hyz) ↔
      rootInverted y B.left :=
  B.slope_lt_iff_inverted_left y _ _ ha hb
    (graphRoot_inverted_target hxy) (graphRoot_not_inverted_source hyz)

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

/-- A nonzero length below an existing greater length has exactly one left
simple descent. This is not asserted for a finite dihedral longest element. -/
theorem unique_leftDescent (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    ∃! i : Bool, cs.IsLeftDescent w i := by
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one (w := w) (by
    intro he
    rw [he,cs.length_one] at hw
    omega)
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  have hj' : j = !i := by cases i <;> cases j <;> simp_all
  have he : cs.wordProd (alt i (cs.length w)) =
      cs.wordProd (alt (!i) (cs.length w)) := by
    rw [← eq_alt_of_descent cs i hi, ← hj', ← eq_alt_of_descent cs j hj]
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs hw hz
  have all_eq (v : W) (hv : cs.length v = cs.length w) : v=w := by
    obtain ⟨k,hk⟩ := exists_alt cs v
    rw [hv] at hk
    have hki : k=i ∨ k=(!i) := by cases k <;> cases i <;> simp
    rcases hki with hki | hki
    · rw [hki] at hk
      exact hk.trans (eq_alt_of_descent cs i hi).symm
    · rw [hki] at hk
      exact hk.trans (he.symm.trans (eq_alt_of_descent cs i hi).symm)
  exact hab ((all_eq a ((hab' a).mpr (.inl rfl))).trans
    (all_eq b ((hab' b).mpr (.inr rfl))).symm)

/-- Internally, the diagram involution interchanges the two unique-descent
vertices of each rank. -/
theorem descent_swap_false_iff_not (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    cs.IsLeftDescent (swap cs w) false ↔ ¬ cs.IsLeftDescent w false := by
  rw [descent_swap]
  obtain ⟨i,hi,hu⟩ := unique_leftDescent cs hw hz
  cases i
  · constructor
    · intro h
      have hh := hu true h
      contradiction
    · exact fun h => (h hi).elim
  · constructor
    · intro _ h
      have hh := hu false h
      contradiction
    · exact fun _ => hi

end
end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The ambient sign of a canonical plane root in a minimal coset is the
intrinsic simple-descent sign, with the original left labels. -/
theorem simpleRoot_inverted_coset_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) (i : Bool) :
    rootInverted ((w : W)*a₀) (B.simpleRoot i) ↔ B.system.IsLeftDescent w i := by
  change (∀ k, action M cs ((w : W)*a₀)⁻¹ (B.simpleRoot i).val k ≤ 0) ↔ _
  rw [root_inversion_coset_iff hmin w.property (B.simpleRoot i).property.1
    (B.simpleRoot_mem i)]
  have hr : Represents M cs (B.system.simple i : W) (B.simpleRoot i).val := by
    rw [B.system_simple]
    exact rootReflection_represents M cs _
  rw [B.inversion_iff hr (B.simpleRoot_mem i) (B.simpleRoot i).property.2 w]
  exact B.system.isLeftInversion_simple_iff_isLeftDescent w i

theorem edgeRoot_plane {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    (B.edgeRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents
    ((B.bruhatStep_iff x y).mpr h))).mp
  exact (planeSubgroup M cs P).mul_mem y.property
    ((planeSubgroup M cs P).inv_mem x.property)

/-- In the intrinsic system, the middle-vertex test uses its actual left
simple generator; it therefore applies to any induced dihedral realization. -/
theorem edgeRoot_slopes_iff {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      B.system.IsLeftDescent y false := by
  unfold edgeRoot
  rw [B.consecutive_slopes_iff ((B.bruhatStep_iff x y).mpr hxy)
    ((B.bruhatStep_iff y z).mpr hyz) (B.edgeRoot_plane hxy) (B.edgeRoot_plane hyz)]
  have hmin : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  simpa only [mul_one, simpleRoot, Bool.false_eq_true, ↓reduceIte] using
    B.simpleRoot_inverted_coset_iff hmin y false

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem simplePositive_injective : Function.Injective (simplePositive (M := M) (cs := cs)) := by
  intro i j hij
  have he := congrArg (fun a : PositiveRoot M cs => a.val i) hij
  by_contra hne
  simp [simplePositive, root, hne] at he

theorem height_positive : PositiveFunctional (height (I := I)) := by
  intro i
  simp [height,root]

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem simple_lower_bound (i : I)
    (hi : ∀ j, O.slope (simplePositive i) ≤ O.slope (simplePositive j))
    (a : PositiveRoot M cs) : O.slope (simplePositive i) ≤ O.slope a := by
  change O.slope (simplePositive i) ≤ O.numerator a.val / O.denominator a.val
  rw [le_div_iff₀ (O.denominator_pos a)]
  rw [dual_coordinate_sum O.numerator a.val, dual_coordinate_sum O.denominator a.val,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := (le_div_iff₀ (O.positive j)).mp (hi j)
  change O.slope (simplePositive i) * O.denominator (root j) ≤ O.numerator (root j) at hj
  nlinarith [mul_nonneg (a.property.2 j) (sub_nonneg.mpr hj)]

theorem exists_least_simple [Nonempty I] : ∃ i : I,
    ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset I)
    (fun i => O.slope (simplePositive i)) Finset.univ_nonempty
  exact ⟨i, O.simple_lower_bound i (fun j => hi j (Finset.mem_univ j))⟩

theorem least_simple_descent {y : W} (hy : y ≠ 1) (ha : O.Adapted y) :
    ∃ i : I, cs.IsLeftDescent y i ∧
      O.slope (simplePositive i) < 0 ∧
      ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨j,hj⟩ := cs.exists_leftDescent_of_ne_one hy
  let : Nonempty I := ⟨j⟩
  obtain ⟨i,hi⟩ := O.exists_least_simple
  have hjr : rootInverted y (simplePositive (M := M) (cs := cs) j) := by
    apply ((rootReflection_represents M cs _).inversion_iff (simplePositive j).property.2 y).mpr
    simpa only [rootRef_simplePositive] using (show cs.IsLeftInversion y (cs.simple j) from
      ⟨cs.isReflection_simple j,hj⟩)
  have hi0 := lt_of_le_of_lt (hi (simplePositive j)) ((ha _).1.mpr hjr)
  refine ⟨i,?_,hi0,hi⟩
  have hir := ((rootReflection_represents M cs _).inversion_iff
    (simplePositive i).property.2 y).mp ((ha _).1.mp hi0)
  simpa only [rootRef_simplePositive, CoxeterSystem.IsLeftDescent] using hir.2


theorem adapted_of_chamber {y : W} (hc : O.Chamber y) : O.Adapted y := by
  let f : Module.Dual ℝ (I → ℝ) := O.numerator.comp (action M cs y).toLinearMap
  have hf : PositiveFunctional f := hc
  intro a
  have he (v : I → ℝ) : f (action M cs y⁻¹ v) = O.numerator v := by
    change O.numerator (action M cs y (action M cs y⁻¹ v)) = _
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases ha : rootInverted y a
  · have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonpos _ _ ha, map_neg, he] at hv
    have hn : O.slope a < 0 := div_neg_of_neg_of_pos (by linarith) (O.denominator_pos a)
    exact ⟨iff_of_true hn ha, hn.ne⟩
  · have hp := (not_rootInverted_iff y a).mp ha
    have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonneg _ _ hp, he] at hv
    have hn : 0 < O.slope a := div_pos hv (O.denominator_pos a)
    exact ⟨iff_of_false (not_lt.mpr hn.le) ha, hn.ne'⟩

end RatioOrder

/-- The generic functional can be chosen in any prescribed Coxeter chamber,
not just outside the countably many equality hyperplanes. The explicit
polynomial perturbation makes both requirements simultaneous. -/
theorem exists_ratioOrder_chamber_height (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y ∧ O.denominator=height := by
  classical
  let := countable_Positiveroot M cs
  let f₀ : Module.Dual ℝ (I → ℝ) := height.comp (action M cs y⁻¹).toLinearMap
  let f : ℝ → Module.Dual ℝ (I → ℝ) := fun t =>
    f₀ + t • ReflectionSchedules.momentFunctional t
  have hf (t : ℝ) (v : I → ℝ) : f t v = f₀ v +
      t * (ReflectionSchedules.coordinatePolynomial v).eval t := by
    simp [f,ReflectionSchedules.coordinatePolynomial_eval]
  let U : Set ℝ := {t | ∀ i, 0 < f t (action M cs y (root i))}
  have hu : IsOpen U := by
    change IsOpen {t | ∀ i, 0 < f t (action M cs y (root i))}
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt continuous_const
    simp only [hf]
    exact continuous_const.add (continuous_id.mul (Polynomial.continuous _))
  have h0 : 0 ∈ U := by
    intro i
    simp only [f,zero_smul,add_zero]
    change 0 < height (action M cs y⁻¹ (action M cs y (root i)))
    rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
    exact height_positive i
  let P := {p : PositiveRoot M cs × PositiveRoot M cs // p.1 ≠ p.2}
  let v : P → (I → ℝ) := fun p => normalizedRoot p.val.1 - normalizedRoot p.val.2
  let d : P → Polynomial ℝ := fun p => Polynomial.C (f₀ (v p)) +
    Polynomial.X * ReflectionSchedules.coordinatePolynomial (v p)
  have hd : ∀ p, d p ≠ 0 := by
    intro p hp
    have hz := congrArg (fun q : Polynomial ℝ => q.eval 0) hp
    have hz' : f₀ (v p) = 0 := by simpa [d] using hz
    have hq : ReflectionSchedules.coordinatePolynomial (v p) = 0 := by
      simpa only [d,hz',Polynomial.C_0,zero_add,mul_eq_zero,Polynomial.X_ne_zero,false_or] using hp
    have hv : v p = 0 := ReflectionSchedules.coordinatePolynomial_injective (by simpa [ReflectionSchedules.coordinatePolynomial] using hq)
    exact p.property (normalizedRoot_injective (sub_eq_zero.mp hv))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion
    (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  obtain ⟨t,htU,ht⟩ := (hbad.dense_compl ℝ).inter_open_nonempty U hu ⟨0,h0⟩
  have hinj : Function.Injective (fun a : PositiveRoot M cs => f t a.val / height a.val) := by
    intro a b heq
    by_contra hab
    apply ht
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(a,b),hab⟩,?_⟩
    change (d ⟨(a,b),hab⟩).eval t = 0
    dsimp only [d]
    rw [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,← hf]
    change f t (normalizedRoot a - normalizedRoot b) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [normalizedRoot,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using heq
  exact ⟨⟨height,f t,height_positive,hinj⟩,htU,rfl⟩

theorem simple_action_nonneg (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : ∀ k, 0 ≤ action M cs (cs.simple i) a.val k := by
  apply a.property.1.act (cs.simple i) |>.sign.resolve_right
  intro hn
  exact ha (Subtype.ext (a.property.1.eq_simple_of_nonpos a.property.2 i hn))

theorem simple_positiveAction_val (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (positiveAction (cs.simple i) a).val = action M cs (cs.simple i) a.val :=
  positiveAction_eq_of_nonneg _ _ (simple_action_nonneg i a ha)

theorem simple_positiveAction_ne (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : positiveAction (cs.simple i) a ≠ simplePositive i := by
  intro he
  apply ha
  exact (positiveActionEquiv (cs.simple i)).injective (he.trans (positiveAction_simplePositive i).symm)

theorem exists_uniform_pos_lt (v : I → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < v i := by
  have aux (s : Finset I) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < v i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hlt⟩ := ih
      refine ⟨min ε (v a / 2),lt_min hε (half_pos (hv a)),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hv i))
      · exact lt_of_le_of_lt (min_le_left _ _) (hlt i hi)
  obtain ⟨ε,hε,hlt⟩ := aux Finset.univ
  exact ⟨ε,hε,fun i => hlt i (Finset.mem_univ i)⟩

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem exists_turn_parameter (i : I) (hi0 : O.slope (simplePositive i) < 0)
    (hi : ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a) :
    ∃ k : ℝ, k < 0 ∧ O.slope (simplePositive i) < k ∧
      PositiveFunctional (O.turnDenominator i k) := by
  let c := O.slope (simplePositive i)
  let v : I → ℝ := fun j => if j=i then -c else
    O.slope (positiveAction (cs.simple i) (simplePositive j)) - c
  have hv : ∀ j, 0 < v j := by
    intro j
    by_cases hj : j=i
    · simp only [v,ite_eq_left hj]
      exact neg_pos.mpr hi0
    · simp only [v,ite_eq_right hj]
      apply sub_pos.mpr
      apply lt_of_le_of_ne (hi _)
      intro he
      exact simple_positiveAction_ne i (simplePositive j)
        (fun hh => hj (simplePositive_injective hh)) (O.slope_injective he.symm)
  obtain ⟨ε,hε,hεv⟩ := exists_uniform_pos_lt v hv
  have hεc : ε < -c := by simpa only [v,ite_eq_left rfl] using hεv i
  refine ⟨c+ε,by linarith,by dsimp [c]; linarith,?_⟩
  intro j
  change 0 < O.numerator (action M cs (cs.simple i) (root j)) -
    (c+ε)*O.denominator (action M cs (cs.simple i) (root j))
  by_cases hj : j=i
  · subst j
    rw [action_simple_root,map_neg,map_neg]
    have hc : c * O.denominator (root i) = O.numerator (root i) := by
      exact div_mul_cancel₀ _ (O.positive i).ne'
    nlinarith [mul_pos hε (O.positive i)]
  · let a := positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) j)
    have ha : a.val = action M cs (cs.simple i) (root j) :=
      simple_positiveAction_val i (simplePositive j) (fun hh => hj (simplePositive_injective hh))
    rw [← ha]
    have hvj : ε < O.slope a - c := by simpa only [v,ite_eq_right hj] using hεv j
    have hlt : c+ε < O.slope a := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ (O.denominator_pos a)).mp hlt)


theorem turn_chamber (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) {y : W} (hy : O.Chamber y) :
    (O.turn i k hk hp).Chamber (cs.simple i * y) := by
  intro j
  change 0 < O.numerator (action M cs (cs.simple i)
    (action M cs (cs.simple i * y) (root j)))
  rw [← LinearEquiv.mul_apply,← map_mul,cs.simple_mul_simple_cancel_left]
  exact hy j

theorem turn_simple_greatest (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope a < (O.turn i k hk.ne hp).slope (simplePositive i) := by
  have hlt : (O.turn i k hk.ne hp).slope a < 1 := by
    apply (div_lt_iff₀ (hp.root_pos a)).mpr
    change O.numerator (action M cs (cs.simple i) a.val) <
      1 * (O.numerator (action M cs (cs.simple i) a.val) -
        k * O.denominator (action M cs (cs.simple i) a.val))
    have hap := O.denominator_pos (positiveAction (cs.simple i) a)
    rw [simple_positiveAction_val i a ha] at hap
    nlinarith [mul_neg_of_neg_of_pos hk hap]
  have hgt : 1 < (O.turn i k hk.ne hp).slope (simplePositive i) := by
    apply (lt_div_iff₀ (hp.root_pos (simplePositive i))).mpr
    change 1 * (O.numerator (action M cs (cs.simple i) (root i)) -
       k * O.denominator (action M cs (cs.simple i) (root i))) <
      O.numerator (action M cs (cs.simple i) (root i))
    rw [action_simple_root,map_neg,map_neg]
    nlinarith [mul_neg_of_neg_of_pos hk (O.positive i)]
  exact hlt.trans hgt

theorem turn_slope_lt_iff (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k))
    (a b : PositiveRoot M cs) (ha : a ≠ simplePositive i) (hb : b ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) a) <
      (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) b) ↔ O.slope a < O.slope b := by
  have hact (a : PositiveRoot M cs) (ha : a ≠ simplePositive i) :
      action M cs (cs.simple i) (positiveAction (cs.simple i) a).val = a.val := by
    rw [simple_positiveAction_val i a ha,← LinearEquiv.mul_apply,← map_mul,
      (cs.isReflection_simple i).mul_self,map_one]
    rfl
  have haD := hp.root_pos (positiveAction (cs.simple i) a)
  have hbD := hp.root_pos (positiveAction (cs.simple i) b)
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) at haD
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) at hbD
  rw [hact a ha] at haD
  rw [hact b hb] at hbD
  change O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val)) <
    O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val)) ↔
    O.numerator a.val / O.denominator a.val < O.numerator b.val / O.denominator b.val
  rw [hact a ha,hact b hb,div_lt_div_iff₀ haD hbD,
    div_lt_div_iff₀ (O.denominator_pos a) (O.denominator_pos b)]
  constructor
  · intro h
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg hk.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  · intro h
    have := mul_neg_of_neg_of_pos hk (sub_pos.mpr h)
    nlinarith

/-- The actual geometric rotation needed for the Hecke recursion. It moves
the least simple root to last and preserves all other root comparisons. -/
theorem exists_rotation {y : W} (hy : y ≠ 1) (hc : O.Chamber y) :
    ∃ (i : I) (O' : RatioOrder (M := M) (cs := cs)),
      cs.IsLeftDescent y i ∧ O'.Chamber (cs.simple i * y) ∧
      (∀ a : PositiveRoot M cs, a ≠ simplePositive i →
        O.slope (simplePositive i) < O.slope a ∧ O'.slope a < O'.slope (simplePositive i)) ∧
      (∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
        (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
          O.slope a < O.slope b)) := by
  obtain ⟨i,hi,hi0,hmin⟩ := O.least_simple_descent hy (O.adapted_of_chamber hc)
  obtain ⟨k,hk,_,hpos⟩ := O.exists_turn_parameter i hi0 hmin
  refine ⟨i,O.turn i k hk.ne hpos,hi,O.turn_chamber i k hk.ne hpos hc,?_,?_⟩
  · intro a ha
    exact ⟨lt_of_le_of_ne (hmin a) (fun he => ha (O.slope_injective he).symm),
      O.turn_simple_greatest i k hk hpos a ha⟩
  · exact O.turn_slope_lt_iff i k hk hpos

end RatioOrder

end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/

namespace KLInvariance.SchedulePaths
variable {V E V' E' : Type*} (source target : E → V) (source' target' : E' → V')

/-- Relabelling graph vertices and edges preserves the actual path predicate. -/
theorem IsPath.map {x y : V} {p : List E}
    (hp : IsPath source target x y p) (f : V → V') (g : E → E')
    (hs : ∀ e, source' (g e) = f (source e))
    (ht : ∀ e, target' (g e) = f (target e)) :
    IsPath source' target' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    exact ⟨(hs e).trans (congrArg f hp.1), ht e ▸ ih hp.2⟩

/-- A path's adjacent comparisons suffice for a transitive label order. The
statement allows the comparison to change under an edge map, provided the
local relation is checked only on composable edges. -/
theorem IsPath.pairwise_map_of_local {Λ Λ' : Type*} [LinearOrder Λ] [LinearOrder Λ']
    {x y : V} {p : List E} (hp : IsPath source target x y p)
    (label : E → Λ) (label' : E' → Λ') (g : E → E')
    (hlocal : ∀ e f, target e = source f →
      label e < label f → label' (g e) < label' (g f))
    (horder : p.Pairwise (fun e f => label e < label f)) :
    (p.map g).Pairwise (fun e f => label' e < label' f) := by
  rw [← List.isChain_iff_pairwise] at horder ⊢
  rw [List.isChain_map]
  induction p generalizing x with
  | nil => exact .nil
  | cons e p ih =>
    cases p with
    | nil => exact .singleton e
    | cons f p =>
      rw [List.isChain_cons_cons] at horder ⊢
      exact ⟨hlocal e f hp.2.1.symm horder.1, ih hp.2 horder.2⟩

end KLInvariance.SchedulePaths

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable
theorem edgeRoot_ne_of_path {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    B.edgeRoot hxy ≠ B.edgeRoot hyz :=
  graphRoot_ne_of_path ((B.bruhatStep_iff x y).mpr hxy) ((B.bruhatStep_iff y z).mpr hyz)

/-- At every internal vertex, the cut switches side under the path involution.
This is the local relation behind rank-two path-product reversal. -/
theorem edgeRoot_slopes_rankFlip {x y z top : planeSubgroup M cs P} {L : ℕ}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z)
    (hL : L < B.system.length y) (hH : B.system.length y < B.system.length top) :
    let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
    let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      geometricSlope (B.edgeRoot hz) < geometricSlope (B.edgeRoot hx) := by
  dsimp only
  let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
  let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
  have hsign : B.system.IsLeftDescent
      (rankFlip B.system L (B.system.length top) y) false ↔
      ¬ B.system.IsLeftDescent y false := by
    rw [rankFlip,ite_eq_left ⟨hL,hH⟩]
    exact descent_swap_false_iff_not B.system (by omega) hH
  have hne : geometricSlope (B.edgeRoot hx) ≠ geometricSlope (B.edgeRoot hz) :=
    fun he => B.edgeRoot_ne_of_path hx hz (geometricSlope_injective he)
  rw [B.edgeRoot_slopes_iff]
  constructor
  · intro hi
    have hn : ¬ geometricSlope (B.edgeRoot hx) < geometricSlope (B.edgeRoot hz) := by
      rw [B.edgeRoot_slopes_iff,hsign]
      exact not_not.mpr hi
    exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm
  · intro hi
    by_contra hn
    have hlt := (B.edgeRoot_slopes_iff hx hz).mpr (hsign.mpr hn)
    exact lt_asymm hlt hi

/-- The global edge map reverses the comparison for every composable pair.
No statement is asserted for disjoint edge labels, which can share ties. -/
theorem intervalEdgeSlope_flip {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi e < B.intervalEdgeSlope lo hi f ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) := by
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  have hl : B.system.length lo < B.system.length ey.val :=
    lt_of_le_of_lt (length_le_of_bruhat B.system ex.property.1) he.1
  have hh : B.system.length ey.val < B.system.length hi :=
    lt_of_lt_of_le hf.1 (length_le_of_bruhat B.system fy.property.2)
  exact B.edgeRoot_slopes_rankFlip he hf hl hh

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.SchedulePaths
open scoped BigOperators
variable {V E R : Type*} (source target : E → V)
noncomputable section

variable [Semiring R]

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_1
theorem dispatch_eq_subpaths_sum (T : R) (schedule : List E) (hnd : schedule.Nodup)
    (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      ∑ p ∈ subpaths source target schedule x y, T ^ p.length := by
  rw [entry_eq_weighted_paths, subpaths, Finset.sum_filter,
    List.sum_toFinset _ (List.nodup_sublists'.mpr hnd)]

/-- A length-preserving involution on the actual schedule-path sets proves
an operator-entry relation, with no Hecke polynomial used in the assumptions. -/
theorem dispatch_eq_of_path_involution (T : R) (schedule schedule' : List E)
    (hnd : schedule.Nodup) (hnd' : schedule'.Nodup) (x y : V) (g : E → E)
    (hg : Function.Involutive g)
    (hforward : ∀ p ∈ subpaths source target schedule x y,
      p.map g ∈ subpaths source target schedule' x y)
    (hbackward : ∀ p ∈ subpaths source target schedule' x y,
      p.map g ∈ subpaths source target schedule x y) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      dispatch source target T (fun z => if z=y then 1 else 0) schedule' x := by
  rw [dispatch_eq_subpaths_sum source target T schedule hnd,
    dispatch_eq_subpaths_sum source target T schedule' hnd']
  exact Finset.sum_nbij' (List.map g) (List.map g) hforward hbackward
    (fun p _ => List.map_involutive_iff.mpr hg p)
    (fun p _ => List.map_involutive_iff.mpr hg p) (fun p _ => by simp)

end
end KLInvariance.SchedulePaths

namespace KLInvariance.SchedulePaths
variable {V E : Type*} (source target : E → V)
noncomputable section

local instance instDecidable_solutions_2_recb270_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Sorted full schedules select precisely their strictly monotone paths;
an actual graph map satisfying the adjacent comparison test transports them. -/
theorem subpaths_map_of_sorted (label label' : E → ℝ)
    (schedule schedule' : List E) (x y : V)
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hs' : schedule'.Pairwise (fun e f => label' f ≤ label' e))
    (hfull' : ∀ e, e ∈ schedule')
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (f : V → V) (g : E → E)
    (hsource : ∀ e, source (g e) = f (source e))
    (htarget : ∀ e, target (g e) = f (target e))
    (hx : f x=x) (hy : f y=y)
    (hlocal : ∀ e f, target e=source f → label f<label e → label' (g f)<label' (g e))
    (p : List E) (hp : p ∈ subpaths source target schedule x y) :
    p.map g ∈ subpaths source target schedule' x y := by
  obtain ⟨hsub,hp⟩ := (mem_subpaths source target schedule x y p).mp hp
  have hstrict := decreasing_of_schedule_path source target label hties hp (hs.sublist hsub)
  have horder := hp.pairwise_map_of_local source target
    (Λ := OrderDual ℝ) (Λ' := OrderDual ℝ)
    (fun e => (label e : OrderDual ℝ)) (fun e => (label' e : OrderDual ℝ)) g hlocal hstrict
  have hp' := hp.map source target source target f g hsource htarget
  rw [hx,hy] at hp'
  exact (mem_subpaths source target schedule' x y (p.map g)).mpr
    ⟨sublist_of_decreasing_subset label' horder hs' (fun _ _ => hfull' _), hp'⟩

end
end KLInvariance.SchedulePaths

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph SchedulePaths

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_1
theorem intervalEdgeSlope_ties {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi) (heq : B.intervalEdgeSlope lo hi e = B.intervalEdgeSlope lo hi f) :
    target B.system lo hi e ≠ source B.system lo hi f := by
  intro hjoin
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  exact B.edgeRoot_ne_of_path he hf (geometricSlope_injective heq)

theorem intervalEdgeSlope_flip_reverse {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi f < B.intervalEdgeSlope lo hi e ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) := by
  have hj : target B.system lo hi (edgeFlip B.system lo hi e) =
      source B.system lo hi (edgeFlip B.system lo hi f) := by
    simpa only [edgeFlip_source,edgeFlip_target] using congrArg (intervalFlip B.system lo hi) hjoin
  simpa only [edgeFlip_involutive B.system lo hi e, edgeFlip_involutive B.system lo hi f] using
    (B.intervalEdgeSlope_flip (edgeFlip B.system lo hi e) (edgeFlip B.system lo hi f) hj).symm

/-- Rank-two reversal of the genuine path-product entry between the two
ends of any full interval. The order is the actual induced angular order. -/
theorem dispatch_reverse_endpoints {R : Type*} [Semiring R]
    {lo hi : planeSubgroup M cs P} (hlohi : BruhatLE B.system lo hi)
    (schedule : List (Edge B.system lo hi)) (hnd : schedule.Nodup)
    (hfull : ∀ e, e ∈ schedule)
    (hs : schedule.Pairwise (fun e f => B.intervalEdgeSlope lo hi f ≤ B.intervalEdgeSlope lo hi e))
    (T : R) :
    let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
    let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule x =
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule.reverse x := by
  dsimp only
  let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
  let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
  have hx : intervalFlip B.system lo hi x=x := Subtype.ext (rankFlip_lower B.system lo hi)
  have hy : intervalFlip B.system lo hi y=y := Subtype.ext (rankFlip_upper B.system lo hi)
  have hrs : schedule.reverse.Pairwise
      (fun e f => -B.intervalEdgeSlope lo hi f ≤ -B.intervalEdgeSlope lo hi e) := by
    rw [List.pairwise_reverse]
    exact hs.imp (fun h => neg_le_neg h)
  have hrfull : ∀ e, e ∈ schedule.reverse := fun e => List.mem_reverse.mpr (hfull e)
  apply dispatch_eq_of_path_involution _ _ T schedule schedule.reverse hnd (List.nodup_reverse.mpr hnd) x y
    (edgeFlip B.system lo hi) (edgeFlip_involutive B.system lo hi)
  · apply subpaths_map_of_sorted _ _ (B.intervalEdgeSlope lo hi)
      (fun e => -B.intervalEdgeSlope lo hi e) schedule schedule.reverse x y hs hrs hrfull
      (B.intervalEdgeSlope_ties) (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact neg_lt_neg ((B.intervalEdgeSlope_flip_reverse e f hj).mp hlt)
  · apply subpaths_map_of_sorted _ _ (fun e => -B.intervalEdgeSlope lo hi e)
      (B.intervalEdgeSlope lo hi) schedule.reverse schedule x y hrs hs hfull
      (fun e f he => B.intervalEdgeSlope_ties e f (neg_injective he))
      (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact (B.intervalEdgeSlope_flip e f hj).mp (neg_lt_neg_iff.mp hlt)

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Genuine Dyer identification for geometric orders adapted to a fixed top.
The path values below are defined from actual reflection edges; equality with
`Hecke.rTilde` will be proved by its genuine simple-descent recurrence. -/
namespace KLInvariance.AdaptedDyer
open TitsSpace SchedulePaths
open scoped BigOperators
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] OAI.KLInvariance.AdaptedDyer.instDecidable_solutions
theorem target_eq_root (e : Edge cs) :
    target cs e = rootRef (rootLabel cs e) * source cs e := by
  rw [rootRef_rootLabel]
  group

theorem rootLabel_ne_of_join (e f : Edge cs) (h : target cs e = source cs f) :
    rootLabel cs e ≠ rootLabel cs f := by
  rcases e with ⟨⟨x,y⟩,he⟩
  rcases f with ⟨⟨z,w⟩,hf⟩
  change y=z at h
  subst z
  exact graphRoot_ne_of_path he hf

variable {cs}

theorem score_ties (O : RatioOrder (M := M) (cs := cs)) (e f : Edge cs)
    (h : score O e = score O f) : target cs e ≠ source cs f :=
  fun hj => rootLabel_ne_of_join cs e f hj (O.slope_injective h)

variable (cs)

variable {cs}

theorem schedule_increasing (O : RatioOrder (M := M) (cs := cs)) (b : W) :
    (schedule O b).Pairwise (fun e f => score O e ≤ score O f) := by
  unfold schedule
  apply List.pairwise_mergeSort'

variable (cs)
omit [Fintype I] in
theorem path_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) : BruhatLE cs x y := by
  induction p generalizing x with
  | nil => exact hp ▸ .refl
  | cons e p ih =>
    exact hp.1 ▸ (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans (ih hp.2)

omit [Fintype I] in
theorem path_targets_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) :
    ∀ e ∈ p, BruhatLE cs (target cs e) y := by
  induction p generalizing x with
  | nil => simp
  | cons e p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact path_le cs hp.2
    · exact ih hp.2 f hf

variable {cs}

@[simp] theorem mem_paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) (p : List (Edge cs)) :
    p ∈ paths O x y ↔ IsPath (source cs) (target cs) x y p ∧
      p.Pairwise (fun e f => score O e < score O f) := by
  rw [paths,mem_subpaths]
  constructor
  · rintro ⟨hsub,hp⟩
    refine ⟨hp,?_⟩
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e f h => score_ties O e f h) hp ((schedule_increasing O y).sublist hsub)
  · rintro ⟨hp,hord⟩
    refine ⟨?_,hp⟩
    apply sublist_of_decreasing_subset (Λ := OrderDual ℝ)
      (fun e => (score O e : OrderDual ℝ)) hord (schedule_increasing O y)
    intro e he
    exact (mem_schedule O y e).mpr (path_targets_le cs hp e he)


variable (cs)
theorem rootRef_injective : Function.Injective (rootRef (M := M) (cs := cs)) := by
  intro a b h
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootLabel_simple_iff (i : I) (e : Edge cs) :
    rootLabel cs e = simplePositive i ↔ target cs e = cs.simple i * source cs e := by
  constructor
  · intro h
    rw [target_eq_root cs e,h,rootRef_simplePositive]
  · intro h
    apply rootRef_injective cs
    rw [rootRef_rootLabel,rootRef_simplePositive,h]
    group

theorem rotateEdge_val (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    (rotateEdge cs i e).val = (cs.simple i * source cs e,cs.simple i * target cs e) := by
  rw [rotateEdge,dite_eq_right (fun hh => h ((rootLabel_simple_iff cs i e).mpr hh))]

theorem rotateEdge_root (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) = positiveAction (cs.simple i) (rootLabel cs e) := by
  apply rootRef_injective cs
  rw [rootRef_rootLabel]
  change (rotateEdge cs i e).val.2 * (rotateEdge cs i e).val.1⁻¹ =
    rootRef (positiveAction (cs.simple i) (rootLabel cs e))
  have hc : rootRef (positiveAction (cs.simple i) (rootLabel cs e)) =
      cs.simple i * rootRef (rootLabel cs e) * (cs.simple i)⁻¹ :=
    rootReflection_positiveAction _ _
  rw [rotateEdge_val cs i e h,hc,rootRef_rootLabel]
  group

theorem rotateEdge_nonsimple (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) ≠ simplePositive i := by
  rw [rotateEdge_root cs i e h]
  exact simple_positiveAction_ne i _ h

@[simp] theorem rotateEdge_involutive (i : I) : Function.Involutive (rotateEdge cs i) := by
  intro e
  by_cases h : rootLabel cs e = simplePositive i
  · have he : rotateEdge cs i e = e := by
      rw [rotateEdge,dite_eq_left ((rootLabel_simple_iff cs i e).mp h)]
    rw [he,he]
  · apply Subtype.ext
    rw [rotateEdge_val cs i _ (rotateEdge_nonsimple cs i e h)]
    change (cs.simple i * (rotateEdge cs i e).val.1,
      cs.simple i * (rotateEdge cs i e).val.2) = e.val
    rw [rotateEdge_val cs i e h]
    simp only [cs.simple_mul_simple_cancel_left]
    rfl

omit [Fintype I] in
theorem path_map_of_mem {E E' V V' : Type*} (src tgt : E → V) (src' tgt' : E' → V')
    {p : List E} {x y : V} (hp : IsPath src tgt x y p) (f : V → V') (g : E → E')
    (hs : ∀ e ∈ p, src' (g e) = f (src e)) (ht : ∀ e ∈ p, tgt' (g e) = f (tgt e)) :
    IsPath src' tgt' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    refine ⟨(hs e List.mem_cons_self).trans (congrArg f hp.1),?_⟩
    rw [ht e List.mem_cons_self]
    exact ih hp.2 (fun a ha => hs a (List.mem_cons_of_mem e ha))
      (fun a ha => ht a (List.mem_cons_of_mem e ha))

theorem path_rotate {x y : W} {p : List (Edge cs)} (i : I)
    (hp : IsPath (source cs) (target cs) x y p)
    (hn : ∀ e ∈ p, rootLabel cs e ≠ simplePositive i) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y) (p.map (rotateEdge cs i)) := by
  apply path_map_of_mem (source cs) (target cs) (source cs) (target cs)
    hp (fun z => cs.simple i*z) (rotateEdge cs i)
  · intro e he
    exact congrArg Prod.fst (rotateEdge_val cs i e (hn e he))
  · intro e he
    exact congrArg Prod.snd (rotateEdge_val cs i e (hn e he))


@[simp] theorem rotateEdge_twice (i : I) (e : Edge cs) :
    rotateEdge cs i (rotateEdge cs i e) = e := rotateEdge_involutive cs i e

variable {cs}

@[simp] theorem nonsimple_map (i : I) {p : List (Edge cs)} (hn : Nonsimple i p) :
    Nonsimple i (p.map (rotateEdge cs i)) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact rotateEdge_nonsimple cs i f (hn f hf)

@[simp] theorem path_map_twice (i : I) (p : List (Edge cs)) :
    (p.map (rotateEdge cs i)).map (rotateEdge cs i) = p := by
  simp only [List.map_map,Function.comp_def,rotateEdge_twice]
  exact List.map_id p

theorem path_rotate_iff (i : I) {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y)
      (p.map (rotateEdge cs i)) ↔ IsPath (source cs) (target cs) x y p := by
  constructor
  · intro hp
    simpa only [cs.simple_mul_simple_cancel_left,path_map_twice] using
      path_rotate cs i hp (nonsimple_map i hn)
  · intro hp
    exact path_rotate cs i hp hn

theorem paths_rotate_iff (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    p.map (rotateEdge cs i) ∈ paths O' (cs.simple i*x) (cs.simple i*y) ↔ p ∈ paths O x y := by
  rw [mem_paths,mem_paths,path_rotate_iff i hn,List.pairwise_map]
  apply and_congr_right
  intro _
  apply List.Pairwise.iff_of_mem
  intro e f he hf
  simpa only [score,rotateEdge_root cs i e (hn e he),rotateEdge_root cs i f (hn f hf)] using
    hcmp (rootLabel cs e) (rootLabel cs f) (hn e he) (hn f hf)

theorem nonsimple_of_greatest (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope a < O.slope (simplePositive i))
    {x y : W} (hy : ¬cs.length (cs.simple i*y) < cs.length y)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  rw [mem_paths] at hp
  rcases hp with ⟨hp,ho⟩
  induction p generalizing x with
  | nil => simp [Nonsimple]
  | cons e p ih =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      cases p with
      | nil =>
        have hy' : target cs e = y := hp.2
        have hr := (rootLabel_simple_iff cs i e).mp he
        have hx' : source cs e = cs.simple i*y := by
          rw [← hy',hr,cs.simple_mul_simple_cancel_left]
        have hl := e.property.1
        change cs.length (source cs e) < cs.length (target cs e) at hl
        rw [hy',hx'] at hl
        exact hy hl
      | cons f p =>
        have hlt := (List.pairwise_cons.mp ho).1 f List.mem_cons_self
        have hle : score O f ≤ O.slope (simplePositive i) := by
          by_cases hf : rootLabel cs f = simplePositive i
          · exact le_of_eq (congrArg O.slope hf)
          · exact (hmax _ hf).le
        have hes : score O e = O.slope (simplePositive i) := congrArg O.slope he
        exact (not_lt_of_ge hle) (hes ▸ hlt)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact ih hp.2 ho.tail f hf

theorem nonsimple_tail_of_least (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {e : Edge cs} {p : List (Edge cs)}
    (ho : (e::p).Pairwise (fun e f => score O e < score O f)) : Nonsimple i p := by
  intro f hf heq
  have hef := (List.pairwise_cons.mp ho).1 f hf
  have he : O.slope (simplePositive i) ≤ score O e := by
    by_cases he : rootLabel cs e = simplePositive i
    · exact le_of_eq (congrArg O.slope he).symm
    · exact (hmin _ he).le
  have hf' : score O f = O.slope (simplePositive i) := congrArg O.slope heq
  exact (not_lt_of_ge he) (hf' ▸ hef)

theorem nonsimple_of_least_descent (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length (cs.simple i*x) < cs.length x)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  obtain ⟨hp,ho⟩ := (mem_paths O x y p).mp hp
  cases p with
  | nil => simp [Nonsimple]
  | cons e p =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      have hr := (rootLabel_simple_iff cs i e).mp he
      have hl := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at hl
      rw [hr,hp.1] at hl
      exact (lt_asymm hx hl)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact nonsimple_tail_of_least O i hmin ho f hf

@[simp] theorem mem_nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (x y : W) (p : List (Edge cs)) :
    p ∈ nonsimplePaths O i x y ↔ p ∈ paths O x y ∧ Nonsimple i p := by
  simp [nonsimplePaths]

theorem sum_nonsimple_rotate (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    ∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length =
      polynomial O' (cs.simple i*x) (cs.simple i*y) := by
  unfold polynomial
  have hasc : ¬cs.length (cs.simple i*(cs.simple i*y)) < cs.length (cs.simple i*y) := by
    rw [cs.simple_mul_simple_cancel_left]
    omega
  apply Finset.sum_bij (fun p _ => p.map (rotateEdge cs i))
  · intro p hp
    obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i x y p).mp hp
    exact (paths_rotate_iff O O' i hcmp hn).mpr hp
  · intro p hp q hq he
    have := congrArg (List.map (rotateEdge cs i)) he
    simpa only [path_map_twice] using this
  · intro q hq
    have hn := nonsimple_of_greatest O' i hmax hasc hq
    refine ⟨q.map (rotateEdge cs i),?_,path_map_twice i q⟩
    have hn' := nonsimple_map i hn
    apply (mem_nonsimplePaths O i x y _).mpr
    refine ⟨?_,hn'⟩
    apply (paths_rotate_iff O O' i hcmp hn').mp
    simpa only [path_map_twice] using hq
  · intro p hp
    simp only [List.length_map]


variable (cs)

@[simp] theorem simpleEdge_root (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    rootLabel cs (simpleEdge cs i x hx) = simplePositive i :=
  (rootLabel_simple_iff cs i _).mpr rfl

variable {cs}
theorem cons_simple_mem (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x))
    {p : List (Edge cs)} (hp : p ∈ nonsimplePaths O i (cs.simple i*x) y) :
    simpleEdge cs i x hx :: p ∈ paths O x y := by
  obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i _ _ _).mp hp
  obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
  apply (mem_paths O _ _ _).mpr
  refine ⟨⟨rfl,hp⟩,List.pairwise_cons.mpr ⟨?_,ho⟩⟩
  intro e he
  change O.slope (rootLabel cs (simpleEdge cs i x hx)) < O.slope (rootLabel cs e)
  rw [simpleEdge_root]
  exact hmin _ (hn e he)

theorem not_nonsimple_iff_cons (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) (p : List (Edge cs)) :
    p ∈ (paths O x y).filter (fun p => ¬Nonsimple i p) ↔
      ∃ q ∈ nonsimplePaths O i (cs.simple i*x) y, p = simpleEdge cs i x hx :: q := by
  constructor
  · intro hp
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
    cases p with
    | nil => exact (hn (by simp [Nonsimple])).elim
    | cons e p =>
      have hnp : Nonsimple i p := nonsimple_tail_of_least O i hmin ho
      have he : rootLabel cs e = simplePositive i := by
        by_contra he
        apply hn
        intro f hf
        rcases List.mem_cons.mp hf with rfl|hf
        · exact he
        · exact hnp f hf
      have heq : e = simpleEdge cs i x hx := by
        apply Subtype.ext
        apply Prod.ext
        · exact hp.1
        · change target cs e = cs.simple i*x
          rw [(rootLabel_simple_iff cs i e).mp he,hp.1]
      subst e
      refine ⟨p,(mem_nonsimplePaths O i _ _ _).mpr ⟨?_,hnp⟩,rfl⟩
      exact (mem_paths O _ _ _).mpr ⟨hp.2,ho.tail⟩
  · rintro ⟨q,hq,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨cons_simple_mem O i hmin hx hq,?_⟩
    intro hn
    exact hn _ List.mem_cons_self (simpleEdge_root cs i x hx)

theorem polynomial_split (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) :
    polynomial O x y =
      (∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length) +
      Polynomial.X * (∑ p ∈ nonsimplePaths O i (cs.simple i*x) y,
        (Polynomial.X : Polynomial ℤ)^p.length) := by
  unfold polynomial
  rw [← Finset.sum_filter_add_sum_filter_not (paths O x y) (Nonsimple i)]
  congr 1
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun p _ => simpleEdge cs i x hx :: p)
  · intro p hp
    exact (not_nonsimple_iff_cons O i hmin hx _).mpr ⟨p,hp,rfl⟩
  · intro p hp q hq he
    exact List.cons.inj he |>.2
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := (not_nonsimple_iff_cons O i hmin hx q).mp hq
    exact ⟨p,hp,rfl⟩
  · intro p hp
    simp only [List.length_cons,pow_succ']

/-- The path expansion satisfies exactly the genuine normalized Hecke
recursion, because the chosen geometric order can be rotated at a descent. -/
theorem polynomial_recursion (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    polynomial O x y = if cs.length (cs.simple i*x) < cs.length x then
      polynomial O' (cs.simple i*x) (cs.simple i*y) else
      polynomial O' (cs.simple i*x) (cs.simple i*y) +
        Polynomial.X * polynomial O' x (cs.simple i*y) := by
  split_ifs with hx
  · have heq : nonsimplePaths O i x y = paths O x y := by
      ext p
      rw [mem_nonsimplePaths]
      exact and_iff_left_of_imp (nonsimple_of_least_descent O i hmin hx)
    rw [← sum_nonsimple_rotate O O' i hmax hcmp x y hy,heq]
    rfl
  · have ha : cs.length x < cs.length (cs.simple i*x) := by
      have := cs.length_simple_mul x i
      omega
    rw [polynomial_split O i hmin ha,
      sum_nonsimple_rotate O O' i hmax hcmp x y hy,
      sum_nonsimple_rotate O O' i hmax hcmp (cs.simple i*x) y hy,
      cs.simple_mul_simple_cancel_left]


@[simp] theorem paths_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    paths O x x = {[]} := by
  ext p
  rw [mem_paths,Finset.mem_singleton]
  cases p with
  | nil => simp [IsPath]
  | cons e p =>
    constructor
    · rintro ⟨hp,_⟩
      have hl := length_le_of_bruhat cs (path_le cs hp.2)
      have he := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at he
      rw [hp.1] at he
      omega
    · simp

@[simp] theorem polynomial_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    polynomial O x x = 1 := by
  simp [polynomial]

theorem polynomial_zero (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (h : ¬BruhatLE cs x y) : polynomial O x y = 0 := by
  have hp : paths O x y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h (path_le cs ((mem_paths O x y p).mp hp).1)
  simp [polynomial,hp]

/-- Dyer's increasing-path formula for a genuine generic geometric order
whose numerator is in the top chamber. The target is the Hecke-defined
normalized R-polynomial, not a renamed path polynomial. -/
theorem polynomial_eq_rTilde (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (hc : O.Chamber y) : polynomial O x y = Hecke.rTilde cs x y := by
  generalize hn : cs.length y = n
  induction n using Nat.strong_induction_on generalizing O x y with
  | h n ih =>
    by_cases hy : y=1
    · subst y
      by_cases hx : x=1
      · subst x
        rw [polynomial_diagonal,Hecke.rTilde_diagonal]
      · have hxy : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          rw [cs.length_one] at hl
          exact hx (cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl))
        rw [polynomial_zero O x 1 hxy,Hecke.rTilde_zero cs x 1 hxy]
    · obtain ⟨i,O',hi,hc',hends,hcmp⟩ := O.exists_rotation hy hc
      have hi' : cs.length (cs.simple i*y) < n := hn ▸ hi
      have hsx := ih _ hi' O' (cs.simple i*x) (cs.simple i*y) hc' rfl
      have hx := ih _ hi' O' x (cs.simple i*y) hc' rfl
      rw [polynomial_recursion O O' i (fun a ha => (hends a ha).1)
        (fun a ha => (hends a ha).2) hcmp x y hi,
        Hecke.rTilde_recursion cs x y i hi,hsx,hx]

end
end KLInvariance.AdaptedDyer

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionOrders
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/

section

namespace KLInvariance.SchedulePaths
open scoped BigOperators
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
variable (source target : E → V) [Semiring R]

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_3
theorem dispatch_append (T : R) (v : V → R) (p q : List E) :
    dispatch source target T v (p ++ q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

theorem dispatch_add (T : R) (v w : V → R) (p : List E) :
    dispatch source target T (v+w) p =
      dispatch source target T v p + dispatch source target T w p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step,Pi.add_apply]
    split_ifs <;> simp [mul_add,add_assoc,add_left_comm,add_comm]

theorem dispatch_mul_right (T c : R) (v : V → R) (p : List E) :
    dispatch source target T (fun x => v x*c) p =
      fun x => dispatch source target T v p x*c := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step]
    split_ifs <;> simp [add_mul,mul_assoc]

theorem dispatch_zero (T : R) (p : List E) : dispatch source target T (0 : V → R) p = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp [step]

theorem dispatch_sum {A : Type*} (T : R) (F : Finset A) (v : A → V → R) (p : List E) :
    dispatch source target T (∑ a ∈ F, v a) p =
      ∑ a ∈ F, dispatch source target T (v a) p := by
  induction F using Finset.induction_on with
  | empty => simp [dispatch_zero]
  | @insert a F ha ih => simp only [Finset.sum_insert ha,dispatch_add,ih]

theorem dispatch_eq_sum_entries [Fintype V] (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ∑ y, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  have hv : v = ∑ y, (fun z => (if z=y then 1 else 0)*v y) := by
    funext z
    simp [Finset.sum_apply]
  conv_lhs => rw [hv]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

/-- A finite lower region is closed under every target occurring in its
edge schedule, so values outside that region never enter its product. -/
theorem dispatch_congr_on (T : R) (S : Set V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ S) (v w : V → R)
    (hvw : ∀ x ∈ S, v x=w x) :
    ∀ x ∈ S, dispatch source target T v p x = dispatch source target T w p x := by
  induction p with
  | nil => exact hvw
  | cons e p ih =>
    have htail := ih (fun f hf => htarget f (List.mem_cons_of_mem _ hf))
    intro x hx
    simp only [dispatch,step,htail x hx,htail (target e) (htarget e List.mem_cons_self)]

theorem dispatch_eq_finite_entries (T : R) (F : Finset V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ F) (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x =
      ∑ y ∈ F, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  let w : V → R := ∑ y ∈ F, (fun z => (if z=y then 1 else 0)*v y)
  have hvw : ∀ z ∈ (F : Set V), v z=w z := by
    intro z hz
    simp [w,Finset.sum_apply,show z ∈ F from hz]
  rw [dispatch_congr_on source target T (F : Set V) p htarget v w hvw x hx]
  dsimp only [w]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

theorem dispatch_eq_of_entries_on (T : R) (F : Finset V) (p q : List E)
    (hp : ∀ e ∈ p, target e ∈ F) (hq : ∀ e ∈ q, target e ∈ F)
    (h : ∀ x ∈ F, ∀ y ∈ F,
      dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x)
    (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x = dispatch source target T v q x := by
  rw [dispatch_eq_finite_entries source target T F p hp v x hx,
    dispatch_eq_finite_entries source target T F q hq v x hx]
  exact Finset.sum_congr rfl (fun y hy => congrArg (fun a => a*v y) (h x hx y hy))

variable {Λ : Type*} [LinearOrder Λ]

/-- A genuine path in a sorted schedule is determined by its edge set and
strict label order. Arbitrary permutations of repeated reflection labels
therefore have no effect. -/
theorem subpaths_eq_of_sorted (label : E → Λ)
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (p q : List E)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    subpaths source target p x y = subpaths source target q x y := by
  ext s
  simp only [mem_subpaths]
  constructor
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hp.sublist hs)) hq
    exact fun e he => (hmem e).mp (hs.subset he)
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hq.sublist hs)) hp
    exact fun e he => (hmem e).mpr (hs.subset he)


variable {V' E' : Type*} (source' target' : E' → V')

theorem IsPath.map_iff (j : V' → V) (hj : Function.Injective j) (J : E' → E)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e)) {x y : V'} {p : List E'} :
    IsPath source target (j x) (j y) (p.map J) ↔ IsPath source' target' x y p := by
  induction p generalizing x with
  | nil => exact hj.eq_iff
  | cons e p ih =>
    change (source (J e)=j x ∧ IsPath source target (target (J e)) (j y) (p.map J)) ↔ _
    rw [hs,ht,ih,hj.eq_iff]
    rfl

theorem exists_list_lift (J : E' → E) (p : List E)
    (h : ∀ e ∈ p, ∃ e', J e'=e) : ∃ p' : List E', p'.map J=p := by
  induction p with
  | nil => exact ⟨[],rfl⟩
  | cons e p ih =>
    obtain ⟨e',he⟩ := h e List.mem_cons_self
    obtain ⟨p',hp⟩ := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    exact ⟨e'::p',by simp [he,hp]⟩

/-- If all actual paths between the specified endpoints lie in a full embedded
subgraph, its full sorted product computes the same entry. -/
theorem dispatch_entry_graph_embedding (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (j : V' → V) (hj : Function.Injective j) (J : E' → E) (hJ : Function.Injective J)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e))
    (p : List E) (q : List E') (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label (J f) ≤ label (J e)))
    (hqfull : ∀ e, e ∈ q) (hJmem : ∀ e, J e ∈ p)
    (x y : V')
    (hpath : ∀ r ∈ subpaths source target p (j x) (j y), ∀ e ∈ r, ∃ e', J e'=e) :
    dispatch source target T (fun z => if z=j y then 1 else 0) p (j x) =
      dispatch source' target' T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source' target' T q hqnd]
  symm
  have hties' : ∀ e f, label (J e)=label (J f) → target' e ≠ source' f := by
    intro e f he hf
    apply hties (J e) (J f) he
    rw [ht,hs,hf]
  apply Finset.sum_bij (fun r _ => r.map J)
  · intro r hr
    obtain ⟨hr,hpr⟩ := (mem_subpaths source' target' q x y r).mp hr
    apply (mem_subpaths source target p (j x) (j y) (r.map J)).mpr
    constructor
    · apply sublist_of_decreasing_subset label
      · rw [List.pairwise_map]
        exact decreasing_of_schedule_path source' target' (label ∘ J) hties' hpr (hq.sublist hr)
      · exact hp
      · intro e he
        obtain ⟨f,_,rfl⟩ := List.mem_map.mp he
        exact hJmem f
    · exact hpr.map source' target' source target j J hs ht
  · intro r _ s _ he
    exact List.map_injective_iff.mpr hJ he
  · intro r hr
    obtain ⟨s,he⟩ := exists_list_lift J r (hpath r hr)
    refine ⟨s,?_,he⟩
    obtain ⟨hrsub,hrpath⟩ := (mem_subpaths source target p (j x) (j y) r).mp hr
    have hspath : IsPath source' target' x y s :=
      (IsPath.map_iff source target source' target' j hj J hs ht).mp (he ▸ hrpath)
    apply (mem_subpaths source' target' q x y s).mpr
    refine ⟨?_,hspath⟩
    apply sublist_of_decreasing_subset (label ∘ J)
    · have hstrict := decreasing_of_schedule_path source target label hties hrpath (hp.sublist hrsub)
      rw [← he,List.pairwise_map] at hstrict
      exact hstrict
    · exact hq
    · exact fun e _ => hqfull e
  · intro r _
    simp

end
end KLInvariance.SchedulePaths

end


section

/-! Linear coordinates on the actual normalized root line. These give the
rank-two geometry of finite wall crossings for genuine root schedules. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_9_recb270_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem normalizedRoot_mem_iff (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    normalizedRoot a ∈ P ↔ a.val ∈ P := by
  constructor
  · intro h
    have hh := P.smul_mem (height a.val) h
    simpa [normalizedRoot,smul_smul,a.height_pos.ne'] using hh
  · exact fun h => P.smul_mem _ h

theorem rootPlane_eq_normalized_span (a b : PositiveRoot M cs) :
    rootPlane a b = Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mp (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mp (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The intersection of a root-plane with the height-one hyperplane is the
actual affine line through the two normalized roots. -/
theorem normalizedRoot_affine {a b c : PositiveRoot M cs}
    (hc : c.val ∈ rootPlane a b) :
    ∃ t : ℝ, normalizedRoot c = t • normalizedRoot a + (1-t) • normalizedRoot b := by
  have hcn : normalizedRoot c ∈ Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
    rw [← rootPlane_eq_normalized_span]
    exact (normalizedRoot_mem_iff _ _).mpr hc
  obtain ⟨t,s,he⟩ := Submodule.mem_span_pair.mp hcn
  have hh := congrArg (height (I := I)) he
  simp only [map_add,map_smul,normalizedRoot_height,smul_eq_mul,mul_one] at hh
  refine ⟨t,?_⟩
  have hs : s=1-t := by linarith
  exact hs ▸ he.symm

/-- On each genuine root plane, every height-normalized linear functional
is an affine function of the fixed angular slope. -/
theorem exists_affine_rootPlane (f : Module.Dual ℝ (I → ℝ))
    (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  let A := geometricSlope a
  let B := geometricSlope b
  let fa := f (normalizedRoot a)
  let fb := f (normalizedRoot b)
  have hAB : A-B ≠ 0 := sub_ne_zero.mpr (fun h => hab (geometricSlope_injective h))
  let c := (fa-fb)/(A-B)
  let d := fb-c*B
  have ha : fa=c*A+d := by
    dsimp [d,c]
    field_simp
    ring
  have hb : fb=c*B+d := by dsimp [d]; ring
  refine ⟨c,d,fun r hr => ?_⟩
  obtain ⟨t,ht⟩ := normalizedRoot_affine hr
  have hf : f (normalizedRoot r) = t*fa+(1-t)*fb := by
    rw [ht]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hg : geometricSlope r = t*A+(1-t)*B := by
    rw [← geometricFunctional_normalizedRoot,ht]
    simp only [map_add,map_smul,geometricFunctional_normalizedRoot,smul_eq_mul]
    rfl
  rw [hf,hg,ha,hb]
  ring

namespace PlaneBasis
local instance instDecidable_solutions_9_recb270_2 (p : Prop) : Decidable p := Classical.propDecidable p
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
theorem exists_affine (f : Module.Dual ℝ (I → ℝ)) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ P →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  simpa only [B.plane_eq] using exists_affine_rootPlane f B.left B.right B.distinct

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Localization of genuine directed paths in a maximal root-plane coset.
The full relative interval is proved to contain every such path. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module SchedulePaths
open AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_2
/-- All edges of a plane-labelled path lie in the full induced relative
interval between its endpoints, with the original ambient labels. -/
theorem path_coordinates {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g : planeSubgroup M cs P) {y : W} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) y p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∃ k : planeSubgroup M cs P, y=(k:W)*a₀ ∧ BruhatLE B.system g k ∧
      ∀ e ∈ p, ∃ l r : planeSubgroup M cs P,
        source cs e=(l:W)*a₀ ∧ target cs e=(r:W)*a₀ ∧
        BruhatLE B.system g l ∧ BruhatStep B.system l r ∧ BruhatLE B.system r k := by
  induction p generalizing g with
  | nil => exact ⟨g,hp.symm,.refl,by simp⟩
  | cons e p ih =>
    have hg : source cs e*a₀⁻¹ ∈ planeSubgroup M cs P := by
      rw [hp.1]
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using g.property
    have hh := mem_coset_of_graphRoot e.property hg (hP e List.mem_cons_self)
    let h : planeSubgroup M cs P := ⟨target cs e*a₀⁻¹,hh⟩
    have heqh : target cs e=(h:W)*a₀ := by dsimp [h]; group
    have he : BruhatStep B.system g h := by
      apply (B.coset_step_iff hmin g h).mp
      rw [← hp.1,← heqh]
      exact e.property
    obtain ⟨k,hky,hk,hbody⟩ := ih h (heqh ▸ hp.2)
      (fun f hf => hP f (List.mem_cons_of_mem _ hf))
    refine ⟨k,hky,(show BruhatLE B.system g h from .single he).trans hk,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨g,h,hp.1,heqh,.refl,he,hk⟩
    · obtain ⟨l,r,hl,hr,hhl,hlr,hrk⟩ := hbody f hf
      exact ⟨l,r,hl,hr,(show BruhatLE B.system g h from .single he).trans hhl,hlr,hrk⟩

theorem intervalToAmbient_injective {a₀ : W} {g k : planeSubgroup M cs P} :
    Function.Injective (B.intervalToAmbient (a₀ := a₀) (g := g) (k := k)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (mul_right_cancel h))

theorem edgeToAmbient_injective {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} :
    Function.Injective (B.edgeToAmbient hmin (g := g) (k := k)) := by
  intro e f h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  exact Prod.ext (B.intervalToAmbient_injective (congrArg Prod.fst hh))
    (B.intervalToAmbient_injective (congrArg Prod.snd hh))

/-- Edge-by-edge lifting of every plane path into the full relative interval.
It is obtained from actual path connectivity, not from ambient comparability
alone (which would not suffice). -/
theorem path_edges_lift {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) ((k:W)*a₀) p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∀ e ∈ p, ∃ e' : BruhatGraph.Edge B.system g k, B.edgeToAmbient hmin e'=e := by
  obtain ⟨k',he,_,hbody⟩ := B.path_coordinates hmin g hp hP
  have hk : k'=k := Subtype.ext (mul_right_cancel he.symm)
  subst k'
  intro e he
  obtain ⟨l,r,hl,hr,hgl,hlr,hrk⟩ := hbody e he
  let vl : Interval B.system g k := ⟨l,hgl,(show BruhatLE B.system l r from .single hlr).trans hrk⟩
  let vr : Interval B.system g k := ⟨r,hgl.trans (.single hlr),hrk⟩
  refine ⟨⟨(vl,vr),hlr⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext hl.symm hr.symm


include B in
/-- Reversal of a complete angular block of genuine ambient edges preserves
all its endpoint entries. Fullness is with respect to the actual root plane,
not to a rank-two subgroup chosen merely to contain two arbitrary reflections. -/
theorem dispatch_plane_reverse {R : Type*} [Semiring R] (T : R) (b : W)
    (p : List (AdaptedDyer.Edge cs)) (hnd : p.Nodup)
    (hfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hs : p.Pairwise (fun e f => geometricSlope (rootLabel cs f) ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p.reverse x := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let g' : planeSubgroup M cs P := ⟨g,hg⟩
  have hx' : x=(g':W)*a₀ := hx
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e f, L e=L f → target cs e ≠ source cs f := by
    intro e f he
    exact fun hj => rootLabel_ne_of_join cs e f hj (geometricSlope_injective he)
  by_cases hex : ∃ r : List (AdaptedDyer.Edge cs),
      IsPath (source cs) (target cs) x y r ∧ ∀ e ∈ r, (rootLabel cs e).val ∈ P
  · obtain ⟨r,hr,hrP⟩ := hex
    obtain ⟨k,hyk,hgk,_⟩ := B.path_coordinates hmin g' (hx' ▸ hr) hrP
    let lo : Interval B.system g' k := ⟨g',.refl,hgk⟩
    let hi : Interval B.system g' k := ⟨k,hgk,.refl⟩
    let j := B.intervalToAmbient (a₀ := a₀) (g := g') (k := k)
    let J := B.edgeToAmbient hmin (g := g') (k := k)
    have hjlo : j lo=x := hx'.symm
    have hjhi : j hi=y := hyk.symm
    let : Fintype (BruhatGraph.Edge B.system g' k) := Fintype.ofFinite _
    let q : List (BruhatGraph.Edge B.system g' k) :=
      Finset.univ.toList.mergeSort (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e)
    have hqnd : q.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
    have hqfull : ∀ e, e ∈ q := by intro e; simp [q]
    have hqs : q.Pairwise (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e) :=
      List.pairwise_mergeSort' _ _
    have hJroot (e : BruhatGraph.Edge B.system g' k) : L (J e)=B.intervalEdgeSlope g' k e := by
      dsimp [L,J,intervalEdgeSlope]
      rw [B.edgeToAmbient_root]
    have hJmem (e : BruhatGraph.Edge B.system g' k) : J e ∈ p := by
      apply (hfull _).mpr
      constructor
      · dsimp [J]
        rw [B.edgeToAmbient_root]
        exact B.edgeRoot_plane e.property
      · have ht : BruhatLE cs ((e.val.2.val:W)*a₀) ((k:W)*a₀) :=
          B.coset_bruhat hmin e.val.2.property.2
        exact ht.trans (hyk ▸ hy)
    have hlift (s : List (AdaptedDyer.Edge cs))
        (hst : ∀ e ∈ s, e ∈ p)
        (hp : IsPath (source cs) (target cs) (j lo) (j hi) s) :
        ∀ e ∈ s, ∃ e' : BruhatGraph.Edge B.system g' k, J e'=e :=
      B.path_edges_lift hmin hp (fun e he => ((hfull e).mp (hst e he)).1)
    have hleft := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T L hties j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p q hnd hqnd hs (by simpa only [hJroot] using hqs) hqfull hJmem lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => hsub.subset he) hpath)
    have hright := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T (fun e => -L e) (fun e f he => hties e f (neg_injective he))
      j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p.reverse q.reverse (List.nodup_reverse.mpr hnd) (List.nodup_reverse.mpr hqnd)
      (by rw [List.pairwise_reverse]; exact hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hqs.imp (fun he => by simpa only [hJroot] using neg_le_neg he))
      (fun e => List.mem_reverse.mpr (hqfull e))
      (fun e => List.mem_reverse.mpr (hJmem e)) lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => List.mem_reverse.mp (hsub.subset he)) hpath)
    rw [hjlo,hjhi] at hleft hright
    rw [hleft,hright]
    exact B.dispatch_reverse_endpoints hgk q hqnd hqfull hqs T
  · have hzero (q : List (AdaptedDyer.Edge cs))
        (hqp : ∀ e ∈ q, e ∈ p) : subpaths (source cs) (target cs) q x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hr
      exact hex ⟨r,hpath,fun e he => ((hfull e).mp (hqp e (hsub.subset he))).1⟩
    rw [dispatch_eq_subpaths_sum _ _ _ _ hnd,
      dispatch_eq_subpaths_sum _ _ _ _ (List.nodup_reverse.mpr hnd),
      hzero p (fun _ he => he),hzero p.reverse (fun _ he => List.mem_reverse.mp he)]

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidableEq_solutions
theorem sortedSchedule_nodup (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem sortedSchedule_pairwise (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Pairwise (fun e f => score f ≤ score e) :=
  List.pairwise_mergeSort' _ _

theorem blockValues_strict (F : Finset E) (primary : E → A) :
    (blockValues F primary).Pairwise (fun a b => b < a) := by
  have hs := Finset.pairwise_sort (F.image primary) (fun a b => b ≤ a)
  have hn := Finset.sort_nodup (F.image primary) (fun a b => b ≤ a)
  exact (List.pairwise_and_iff.mpr ⟨hs,hn⟩).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)

theorem groupedSchedule_nodup (F : Finset E) (primary : E → A) (score : E → Λ) :
    (groupedSchedule F primary score).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_nodup _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro e hea heb
    have ha := ((mem_scheduleBlock F primary score a e).mp hea).2
    have hb := ((mem_scheduleBlock F primary score b e).mp heb).2
    exact hab.ne (hb.symm.trans ha)

theorem groupedSchedule_pairwise (F : Finset E) (primary : E → A) (score : E → Λ)
    (h : ∀ e ∈ F, ∀ f ∈ F, primary f < primary e → score f ≤ score e) :
    (groupedSchedule F primary score).Pairwise (fun e f => score f ≤ score e) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_pairwise _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab e he f hf
    obtain ⟨he,heq⟩ := (mem_scheduleBlock F primary score a e).mp he
    obtain ⟨hf,hfq⟩ := (mem_scheduleBlock F primary score b f).mp hf
    exact h e he f hf (by simpa only [heq,hfq] using hab)

variable {V : Type*} {R : Type*} [Semiring R] (source target : E → V)

theorem dispatch_entries_eq_of_sorted (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (p q : List E) (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source target T q hqnd,
    subpaths_eq_of_sorted source target label hties p q hp hq hmem x y]

omit [LinearOrder A] in
/-- Replacement on a finite lower region requires no artificial finiteness
assumption on the ambient Coxeter group. -/
theorem dispatch_flatMap_eq_on (T : R) (S : Set V) (blocks : List A) (p q : A → List E)
    (htarget : ∀ a ∈ blocks, ∀ e ∈ p a, target e ∈ S)
    (h : ∀ a ∈ blocks, ∀ v, ∀ x ∈ S,
      dispatch source target T v (p a) x = dispatch source target T v (q a) x)
    (v : V → R) : ∀ x ∈ S,
    dispatch source target T v (blocks.flatMap p) x =
      dispatch source target T v (blocks.flatMap q) x := by
  induction blocks with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro x hx
    simp only [List.flatMap_cons,dispatch_append]
    rw [dispatch_congr_on source target T S (p a) (htarget a List.mem_cons_self)
      _ _ (ih (fun b hb => htarget b (List.mem_cons_of_mem _ hb))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))) x hx]
    exact h a List.mem_cons_self _ x hx

end
end KLInvariance.SchedulePaths

end


section

/-! The actual rank-two edge product is independent of every linear
functional restricted to that root plane, including a wall tie refinement. -/
namespace KLInvariance.TitsSpace
open Module SchedulePaths AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_10
theorem lexRootScore_injective (f : Module.Dual ℝ (I → ℝ)) :
    Function.Injective (lexRootScore (M := M) (cs := cs) f) := by
  intro a b hab
  apply geometricSlope_injective
  exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).2) hab

theorem lexEdgeScore_ties (f : Module.Dual ℝ (I → ℝ)) (e e' : AdaptedDyer.Edge cs)
    (he : lexEdgeScore f e=lexEdgeScore f e') : target cs e ≠ source cs e' := by
  intro hj
  exact rootLabel_ne_of_join cs e e' hj (lexRootScore_injective f he)

omit [Fintype I] in
theorem lex_affine_nonneg {c d x y : ℝ} (hc : 0 ≤ c)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : x ≤ y := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : y < x := lt_of_not_ge hn
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy.le)]
  · exact h.2

omit [Fintype I] in
theorem lex_affine_neg {c d x y : ℝ} (hc : c < 0)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : y ≤ x := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : x < y := lt_of_not_ge hn
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr hxy.le)]
  · have he : x=y := by nlinarith [h.1]
    exact he.symm.le

namespace PlaneBasis
attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_10
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
/-- Any linearly sorted full plane block is either angularly sorted or
reverse-angularly sorted. This includes tied primary labels refined by the
fixed genuine geometric functional. -/
theorem lex_block_orientation (f : Module.Dual ℝ (I → ℝ))
    (p : List (AdaptedDyer.Edge cs))
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P)
    (hs : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e)) :
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)) ∨
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e) ≤ geometricSlope (rootLabel cs e')) := by
  obtain ⟨c,d,hf⟩ := B.exists_affine f
  have hv (e : AdaptedDyer.Edge cs) (he : e ∈ p) :
      lexEdgeScore f e=toLex (c*geometricSlope (rootLabel cs e)+d,geometricSlope (rootLabel cs e)) := by
    unfold lexEdgeScore lexRootScore
    rw [hf _ (hP e he)]
  by_cases hc : 0 ≤ c
  · left
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_nonneg hc hee'
  · right
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_neg (lt_of_not_ge hc) hee'

include B in
/-- A complete plane block, sorted by any functional, has precisely the
same actual path product as its angularly sorted version. -/
theorem dispatch_plane_functional {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (p q : List (AdaptedDyer.Edge cs))
    (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hpfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hqfull : ∀ e, e ∈ q ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hp : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e))
    (hq : q.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) q x := by
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
    intro e e' he hj
    exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
  rcases B.lex_block_orientation f p (fun e he => ((hpfull e).mp he).1) hp with hs|hs
  · exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties
      p q hpnd hqnd hs hq (fun e => (hpfull e).trans (hqfull e).symm) x y
  · have hentry := dispatch_entries_eq_of_sorted (source cs) (target cs) T
      (fun e => -L e) (fun e e' he => hties e e' (neg_injective he))
      p q.reverse hpnd (List.nodup_reverse.mpr hqnd)
      (hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hq.imp (fun he => neg_le_neg he))
      (fun e => (hpfull e).trans ((hqfull e).symm.trans List.mem_reverse.symm)) x y
    exact hentry.trans (B.dispatch_plane_reverse T b q hqnd hqfull hq x y hy).symm

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Generic pencils of genuine linear root-label functionals. At a wall all
roots of a tied block belong to one full actual root plane. -/
namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

/-- A countable family of nonzero vectors can be simultaneously avoided. -/
theorem exists_avoiding_functional {A : Type v} [Countable A] (v : A → (I → ℝ)) :
    ∃ f : Module.Dual ℝ (I → ℝ), ∀ a, v a ≠ 0 → f (v a) ≠ 0 := by
  classical
  let P := {a : A // v a ≠ 0}
  have hn (a : P) : coordinatePolynomial (v a.val) ≠ 0 := by
    intro h
    apply a.property
    apply coordinatePolynomial_injective
    simpa [coordinatePolynomial] using h
  let bad : Set ℝ := ⋃ a : P, {t | (coordinatePolynomial (v a.val)).IsRoot t}
  have hb : bad.Countable := Set.countable_iUnion
    (fun a => (Polynomial.finite_setOfPred_isRoot (hn a)).countable)
  obtain ⟨t,ht⟩ : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have he : bad=Set.univ := Set.eq_univ_of_forall h
    rw [he] at hb
    exact Set.not_countable_univ hb
  refine ⟨momentFunctional t,fun a ha he => ht ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨a,ha⟩,?_⟩
  simpa only [Set.mem_ofPred_eq,Polynomial.IsRoot,coordinatePolynomial_eval] using he

end
end KLInvariance.ReflectionSchedules

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_11
omit [Fintype I] in
theorem pencil_apply (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) (v : I → ℝ) :
    pencil f g t v=(1-t)*f v+t*g v := rfl

theorem pencil_tie_plane (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (t : ℝ)
    (a b : PositiveRoot M cs) (hab : a ≠ b)
    (he : pencil f g t (normalizedRoot a)=pencil f g t (normalizedRoot b)) :
    ∀ c : PositiveRoot M cs,
      pencil f g t (normalizedRoot c)=pencil f g t (normalizedRoot a) ↔
        c.val ∈ rootPlane a b := by
  let v := rootDifference a b
  have hv : f v ≠ 0 := by
    change f (normalizedRoot b-normalizedRoot a) ≠ 0
    rw [map_sub,sub_ne_zero]
    exact fun h => hab (hf h).symm
  have hvt : (1-t)*f v+t*g v=0 := by
    rw [← pencil_apply]
    change pencil f g t (normalizedRoot b-normalizedRoot a)=0
    rw [map_sub,he,sub_self]
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp only [sub_zero,one_mul,zero_mul,add_zero] at hvt
    exact hv hvt
  intro c
  constructor
  · intro hc
    let w := rootDifference a c
    have hwt : (1-t)*f w+t*g w=0 := by
      rw [← pencil_apply]
      change pencil f g t (normalizedRoot c-normalizedRoot a)=0
      rw [map_sub,hc,sub_self]
    have hz : g (wallVector f a b c)=0 := by
      change g (f v • w-f w • v)=0
      rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      apply (mul_eq_zero.mp (show t * (f v*g w-f w*g v)=0 by
        calc
          _ = f v*((1-t)*f w+t*g w)-f w*((1-t)*f v+t*g v) := by ring
          _ = 0 := by rw [hwt,hvt]; ring)).resolve_left ht
    have heq : f v • w=f w • v := sub_eq_zero.mp (hg a b c hz)
    let P := rootPlane a b
    have haP : normalizedRoot a ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert _ _))
    have hbP : normalizedRoot b ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hvP : v ∈ P := P.sub_mem hbP haP
    have hwP : w ∈ P := by
      have hh := P.smul_mem (f v)⁻¹ (heq ▸ P.smul_mem (f w) hvP)
      simpa only [smul_smul,inv_mul_cancel₀ hv,one_smul] using hh
    apply (normalizedRoot_mem_iff P c).mp
    have hh := P.add_mem hwP haP
    simpa only [w,rootDifference,sub_add_cancel] using hh
  · intro hc
    obtain ⟨s,hs⟩ := normalizedRoot_affine hc
    rw [hs,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,← he]
    ring

/-- One intermediate functional is simultaneously transverse to any two
specified generic endpoints, even with infinitely many positive roots. -/
theorem exists_common_transverse (f h : Module.Dual ℝ (I → ℝ)) :
    ∃ g : Module.Dual ℝ (I → ℝ),
      Function.Injective (fun a : PositiveRoot M cs => g (normalizedRoot a)) ∧
      Transverse (M := M) (cs := cs) f g ∧ Transverse (M := M) (cs := cs) h g := by
  let := countable_Positiveroot M cs
  let E := PositiveRoot M cs
  let A := (E × E) ⊕ (Bool × E × E × E)
  let v : A → (I → ℝ) := fun x => match x with
    | .inl (a,b) => rootDifference a b
    | .inr (i,a,b,c) => wallVector (if i then f else h) a b c
  obtain ⟨g,hg⟩ := ReflectionSchedules.exists_avoiding_functional v
  refine ⟨g,?_,?_,?_⟩
  · intro a b he
    by_contra hab
    have hn : rootDifference a b ≠ 0 := by
      exact fun hz => hab (normalizedRoot_injective (sub_eq_zero.mp hz)).symm
    apply hg (.inl (a,b)) hn
    simp only [v,rootDifference,map_sub,he,sub_self]
  · intro a b c he
    by_contra hz
    exact hg (.inr (true,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)
  · intro a b c he
    by_contra hz
    exact hg (.inr (false,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)

end
end KLInvariance.TitsSpace

end


section

/-! Finite wall crossing for actual reflection-edge path matrices. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
open scoped Topology
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.WallDyer.instDecidable_solutions
/-- The complete tied block at any genuine simple wall has an actual
operator independent of the linear tie-breaking functional. -/
theorem block_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (a : ℝ) (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g) a) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h) a) x := by
  let F := (edgeFinset cs b).filter (fun e => rootValue f e=a)
  let p := sortedSchedule F (lexEdgeScore g)
  let q := sortedSchedule F (lexEdgeScore h)
  let r := sortedSchedule F (fun e => geometricSlope (rootLabel cs e))
  change dispatch (source cs) (target cs) T _ p x = dispatch (source cs) (target cs) T _ q x
  have hmem (k : Edge cs) : k ∈ F ↔ BruhatLE cs (target cs k) b ∧ rootValue f k=a := by
    simp only [F,Finset.mem_filter,mem_edgeFinset]
  by_cases hex : ∃ e ∈ F, ∃ e' ∈ F, rootLabel cs e ≠ rootLabel cs e'
  · obtain ⟨e,he,e',he',hne⟩ := hex
    obtain ⟨B⟩ := nonempty_planeBasis (rootLabel cs e) (rootLabel cs e') hne
    have hv := hf (rootLabel cs e) (rootLabel cs e') hne
      (((hmem e).mp he).2.trans ((hmem e').mp he').2.symm)
    have hfull (k : Edge cs) : k ∈ F ↔
        (rootLabel cs k).val ∈ rootPlane (rootLabel cs e) (rootLabel cs e') ∧
        BruhatLE cs (target cs k) b := by
      rw [hmem,← hv,show f (normalizedRoot (rootLabel cs e))=a from ((hmem e).mp he).2]
      exact and_comm
    have hp := B.dispatch_plane_functional T b g p r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    have hq := B.dispatch_plane_functional T b h q r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    exact hp.trans hq.symm
  · have heq (e : Edge cs) (he : e ∈ F) (e' : Edge cs) (he' : e' ∈ F) :
        rootLabel cs e=rootLabel cs e' := by
      by_contra hn
      exact hex ⟨e,he,e',he',hn⟩
    let L : Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
    have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
      intro e e' he hj
      exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
    have hs (s : Module.Dual ℝ (I → ℝ)) :
        (sortedSchedule F (lexEdgeScore s)).Pairwise (fun e e' => L e' ≤ L e) := by
      apply (sortedSchedule_pairwise F (lexEdgeScore s)).imp_of_mem
      intro e e' he he' _
      have hr := heq e ((mem_sortedSchedule _ _ _).mp he) e' ((mem_sortedSchedule _ _ _).mp he')
      exact (congrArg geometricSlope hr).symm.le
    exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties p q
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _) (hs g) (hs h)
      (fun e => (mem_sortedSchedule _ _ e).trans (mem_sortedSchedule _ _ e).symm) x y

/-- All blocks may be replaced simultaneously on the finite lower region. -/
theorem grouped_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (x y : W) (hx : BruhatLE cs x b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore h)) x := by
  let K := lowerFinset cs b
  have ht (s : Module.Dual ℝ (I → ℝ)) (a : ℝ) (e : Edge cs)
      (he : e ∈ scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore s) a) :
      target cs e ∈ K := by
    exact (mem_lowerFinset cs b _).mpr ((mem_edgeFinset cs b e).mp
      ((mem_scheduleBlock _ _ _ _ _).mp he).1)
  apply dispatch_flatMap_eq_on (source cs) (target cs) T (K : Set W)
    (blockValues (edgeFinset cs b) (rootValue f))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h))
    (fun a _ e he => ht g a e he) _ _ x ((mem_lowerFinset cs b x).mpr hx)
  intro a _ v z hz
  apply dispatch_eq_of_entries_on (source cs) (target cs) T K _ _ (ht g a) (ht h a) _ v z hz
  intro l _ k hk
  exact block_entry_independent T b f hf g h a l k ((mem_lowerFinset cs b k).mp hk)

/-- Stable strict primary comparisons identify the genuine sorted schedule
with the corresponding product of tied blocks. -/
theorem entry_eq_grouped {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (h : ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue f e' < rootValue f e → rootValue g e' < rootValue g e)
    (x y : W) :
    entry (cs := cs) T g b x y =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x := by
  apply dispatch_entries_eq_of_sorted (source cs) (target cs) T (lexEdgeScore g)
    (lexEdgeScore_ties g) _ _ (sortedSchedule_nodup _ _) (groupedSchedule_nodup _ _ _)
    (sortedSchedule_pairwise _ _)
  · apply groupedSchedule_pairwise
    intro e he e' he' hlt
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (h e he e' he' hlt))
  · intro e
    simp only [mem_sortedSchedule,mem_groupedSchedule]

theorem pencil_strict_stable (b : W) (f g : Module.Dual ℝ (I → ℝ)) (t₀ : ℝ) :
    ∀ᶠ t in 𝓝 t₀, ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e →
        rootValue (pencil f g t) e' < rootValue (pencil f g t) e := by
  apply (Filter.eventually_all_finset _).mpr
  intro e _
  apply (Filter.eventually_all_finset _).mpr
  intro e' _
  have hc (k : Edge cs) : Continuous (fun t : ℝ => rootValue (pencil f g t) k) := by
    change Continuous (fun t : ℝ => (1-t)*f (normalizedRoot (rootLabel cs k))+
      t*g (normalizedRoot (rootLabel cs k)))
    fun_prop
  by_cases hlt : rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e
  · filter_upwards [(isOpen_lt (hc e') (hc e)).mem_nhds hlt] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall (fun _ h => (hlt h).elim)

/-- Crossing all actual root-plane walls leaves the full path matrix fixed,
not merely a single adapted endpoint column. -/
theorem locally_constant_pencil {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (x y : W) (hx : BruhatLE cs x b) :
    IsLocallyConstant (fun t : ℝ => entry (cs := cs) T (pencil f g t) b x y) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t₀
  filter_upwards [pencil_strict_stable b f g t₀] with t ht
  have hp : rootPlaneTies (M := M) (cs := cs) (pencil f g t₀) := by
    intro a d had he
    exact pencil_tie_plane f g hf hg t₀ a d had he
  rw [entry_eq_grouped T b (pencil f g t₀) (pencil f g t) ht,
    entry_eq_grouped T b (pencil f g t₀) (pencil f g t₀) (fun _ _ _ _ h => h)]
  exact grouped_entry_independent T b (pencil f g t₀) hp (pencil f g t) (pencil f g t₀) x y hx

/-- Full matrix order independence for genuine finite geometric orders. -/
theorem entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f h : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hh : Function.Injective (fun a : PositiveRoot M cs => h (normalizedRoot a)))
    (x y : W) (hx : BruhatLE cs x b) : entry (cs := cs) T f b x y=entry (cs := cs) T h b x y := by
  obtain ⟨g,_,hfg,hhg⟩ := exists_common_transverse (M := M) (cs := cs) f h
  have he := (locally_constant_pencil T b f g hf hfg x y hx).apply_eq_of_preconnectedSpace 0 1
  have he' := (locally_constant_pencil T b h g hh hhg x y hx).apply_eq_of_preconnectedSpace 0 1
  simp only [pencil_zero,pencil_one] at he he'
  exact he.trans he'.symm

end
end KLInvariance.WallDyer

end


section

/-! Dyer's full path-matrix identity, for the same geometric schedule in
every endpoint column, with the genuine Hecke-defined normalized R. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_1_recb270_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem neg_numerator_normalized (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (a : PositiveRoot M cs) :
    (-O.numerator) (normalizedRoot a) = -O.slope a := by
  simp only [LinearMap.neg_apply,dual_normalizedRoot,RatioOrder.slope,hh]

/-- An upper bound larger than the path endpoint creates no extra paths:
every actual directed path stays inside its endpoint interval. -/
theorem subpaths_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    subpaths (source cs) (target cs) (WallDyer.schedule (-O.numerator) b) x y =
      paths O x y := by
  have hscore (e : Edge cs) : rootValue (-O.numerator) e = -score O e :=
    neg_numerator_normalized O hh (rootLabel cs e)
  ext p
  rw [mem_subpaths,mem_paths]
  constructor
  · rintro ⟨hsub,hpath⟩
    refine ⟨hpath,?_⟩
    have hs := (sortedSchedule_pairwise (edgeFinset cs b) (lexEdgeScore (-O.numerator))).sublist hsub
    have hs' : p.Pairwise (fun e e' => score O e ≤ score O e') := by
      apply hs.imp
      intro e e' he
      have hm := Prod.Lex.monotone_fst _ _ he
      change rootValue (-O.numerator) e' ≤ rootValue (-O.numerator) e at hm
      rw [hscore e',hscore e] at hm
      exact neg_le_neg_iff.mp hm
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e e' he => score_ties O e e' he) hpath hs'
  · rintro ⟨hpath,hord⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset (lexEdgeScore (-O.numerator))
    · apply hord.imp
      intro e e' he
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      change rootValue (-O.numerator) e' < rootValue (-O.numerator) e
      rw [hscore e',hscore e]
      exact neg_lt_neg he
    · exact sortedSchedule_pairwise _ _
    · intro e he
      apply (mem_sortedSchedule _ _ _).mpr
      exact (mem_edgeFinset cs b e).mpr ((path_targets_le cs hpath e he).trans hy)

theorem entry_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (-O.numerator) b x y =
      polynomial O x y := by
  unfold entry
  rw [dispatch_eq_subpaths_sum _ _ _ _ (show (WallDyer.schedule (-O.numerator) b).Nodup from sortedSchedule_nodup _ _),
    subpaths_neg_numerator O hh b x y hy]
  rfl


theorem entry_eq_rTilde (f : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) f b x y = Hecke.rTilde cs x y := by
  obtain ⟨O,hO,hh⟩ := exists_ratioOrder_chamber_height (M := M) (cs := cs) y
  have hn : Function.Injective (fun a : PositiveRoot M cs => (-O.numerator) (normalizedRoot a)) := by
    intro a b he
    change (-O.numerator) (normalizedRoot a) = (-O.numerator) (normalizedRoot b) at he
    rw [neg_numerator_normalized O hh a,neg_numerator_normalized O hh b] at he
    exact O.slope_injective (neg_injective he)
  rw [entry_independent (Polynomial.X : Polynomial ℤ) b f (-O.numerator) hf hn x y hx,
    entry_neg_numerator O hh b x y hy,polynomial_eq_rTilde O x y hO]

/-- The manuscript's fixed geometric functional provides such a genuine
full Dyer schedule for every finite lower Bruhat region. -/
theorem geometric_entry_eq_rTilde (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (geometricFunctional (M := M) (cs := cs)) b x y =
      Hecke.rTilde cs x y := by
  apply entry_eq_rTilde _ _ b x y hx hy
  simpa only [geometricFunctional_normalizedRoot] using
    (geometricSlope_injective (M := M) (cs := cs))

end
end KLInvariance.WallDyer

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
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_6
omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_injective : Function.Injective (transportedEdge φ) := by
  intro e f h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact Prod.ext (φ.injective (Subtype.ext (congrArg Prod.fst hh)))
    (φ.injective (Subtype.ext (congrArg Prod.snd hh)))

omit [Fintype I] in
 theorem transportedSchedule_nodup : (transportedSchedule φ).Nodup := by
  unfold transportedSchedule
  exact sortedSchedule_nodup _ _

omit [Fintype I] in
 theorem transportedSchedule_full (e : Edge cs u b) : e ∈ transportedSchedule φ := by
  let := Fintype.ofFinite (Edge cs u b)
  unfold transportedSchedule
  exact (mem_sortedSchedule _ _ _).mpr (Finset.mem_univ _)

omit [Fintype I] in
 theorem transportedSchedule_pairwise : (transportedSchedule φ).Pairwise
     (fun e f => transportedScore φ f ≤ transportedScore φ e) := by
  unfold transportedSchedule
  exact sortedSchedule_pairwise _ _

omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_lift (e : AdaptedDyer.Edge cs')
    (hu : BruhatLE cs' u' (AdaptedDyer.source cs' e))
    (hb : BruhatLE cs' (AdaptedDyer.target cs' e) b') : ∃ f, transportedEdge φ f=e := by
  let x : Interval cs' u' b' := ⟨AdaptedDyer.source cs' e,hu,
    (show BruhatLE cs' (AdaptedDyer.source cs' e) (AdaptedDyer.target cs' e) from
      .single e.property).trans hb⟩
  let y : Interval cs' u' b' := ⟨AdaptedDyer.target cs' e,
    hu.trans (.single e.property),hb⟩
  let f : Edge cs u b := ⟨(φ.symm x,φ.symm y),
    (intervalIso_bruhatStep_iff_general cs' cs φ.symm x y).mpr e.property⟩
  refine ⟨f,?_⟩
  apply Subtype.ext
  change ((φ (φ.symm x)).val,(φ (φ.symm y)).val)=e.val
  rw [φ.apply_symm_apply,φ.apply_symm_apply]
  rfl

omit [Fintype I] in
 theorem transported_dispatch_entry {R : Type*} [Semiring R] (T : R)
    (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T (fun z => if z=y then 1 else 0)
      (transportedSchedule φ) x =
    WallDyer.entry (cs := cs') T (geometricFunctional (M := M') (cs := cs'))
      b' (φ x).val (φ y).val := by
  have hsource {z w : W'} {p : List (AdaptedDyer.Edge cs')}
      (hp : IsPath (AdaptedDyer.source cs') (AdaptedDyer.target cs') z w p) :
      ∀ e ∈ p, BruhatLE cs' z (AdaptedDyer.source cs' e) := by
    induction p generalizing z with
    | nil => simp
    | cons e p ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hp.1 ▸ bruhat_refl cs' z
      · rw [← hp.1]
        exact (show BruhatLE cs' (AdaptedDyer.source cs' e)
          (AdaptedDyer.target cs' e) from .single e.property).trans (ih hp.2 f hf)
  symm
  apply dispatch_entry_graph_embedding (AdaptedDyer.source cs') (AdaptedDyer.target cs')
    (source cs u b) (target cs u b) T
    (lexEdgeScore (geometricFunctional (M := M') (cs := cs')))
    (lexEdgeScore_ties _) (fun z : Interval cs u b => (φ z).val)
    (fun _ _ h => φ.injective (Subtype.ext h)) (transportedEdge φ)
    (transportedEdge_injective φ) (fun _ => rfl) (fun _ => rfl)
    (WallDyer.schedule (geometricFunctional (M := M') (cs := cs')) b')
    (transportedSchedule φ) (sortedSchedule_nodup _ _)
    (transportedSchedule_nodup φ) (sortedSchedule_pairwise _ _)
    (transportedSchedule_pairwise φ) (transportedSchedule_full φ)
  · intro e
    exact (mem_sortedSchedule _ _ _).mpr ((AdaptedDyer.mem_edgeFinset cs' b' _).mpr
      (φ (target cs u b e)).property.2)
  · intro r hr e he
    have hp := ((mem_subpaths _ _ _ _ _ r).mp hr).2
    exact transportedEdge_lift φ e ((φ x).property.1.trans (hsource hp e he))
      ((AdaptedDyer.path_targets_le cs' hp e he).trans (φ y).property.2)

omit [Fintype I] in

 theorem transported_entry_eq_rTilde (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) (Polynomial.X : Polynomial ℤ)
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Hecke.rTilde cs' (φ x).val (φ y).val := by
  rw [transported_dispatch_entry]
  exact WallDyer.geometric_entry_eq_rTilde b' (φ x).val (φ y).val
    (φ x).property.2 (φ y).property.2

end
end KLInvariance.BruhatGraph

end


section

/-! Actual transported numerical R-tilde matrix and its genuine KL reciprocal
vector. No sheaf or desired invariance conclusion is assumed. -/
namespace KLInvariance.SchedulePaths
universe u v w w'
variable {V : Type u} {E : Type v} {R : Type w} {S : Type w'}
  [Semiring R] [Semiring S] (source target : E → V)
noncomputable section

 attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_5
theorem dispatch_map (f : R →+* S) (T : R) (v : V → R) (p : List E) (x : V) :
    f (dispatch source target T v p x) =
      dispatch source target (f T) (fun z => f (v z)) p x := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,step,map_add]
    split_ifs <;> simp only [map_mul,map_zero,ih]

end
end KLInvariance.SchedulePaths

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_7
theorem transported_entry_eval {C : Type*} [CommSemiring C] (T : C)
    (x y : Interval cs u b) (f : ℤ →+* C) :
    dispatch (source cs u b) (target cs u b) T
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) := by
  rw [← transported_entry_eq_rTilde φ x y]
  have h := dispatch_map (source cs u b) (target cs u b) (Polynomial.eval₂RingHom f T)
    Polynomial.X (fun z : Interval cs u b => if z=y then 1 else 0) (transportedSchedule φ) x
  simpa using h.symm

 theorem transported_dispatch_matrix {C : Type*} [CommSemiring C] (T : C)
    (f : ℤ →+* C) (v : Interval cs u b → C) (x : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T v (transportedSchedule φ) x =
      ∑ᶠ y : Interval cs u b,
        Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) * v y := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  rw [dispatch_eq_sum_entries,finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun a => a*v y)
    (transported_entry_eval φ T x y f))

end
end KLInvariance.BruhatGraph

end


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


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

/-! The genuine BMP local intersection map. All freeness, kernel-minimality and
inverse grading assertions here are now unconditional consequences of the
constructed integral duality. The nonvanishing/Hodge input is deliberately
NOT asserted; the last theorem records precisely how it would force the
strict KL halfdegree bound on ACTUAL homogeneous stalk generators. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 theorem actualSectionDuality_homogeneous (i j : ℤ)
    (m n : (ActualBoundary cs b basis).sheaf.sections Set.univ)
    (hm : m ∈ ((ActualBoundary cs b basis).sheaf.sections Set.univ).piece i)
    (hn : n ∈ ((ActualBoundary cs b basis).sheaf.sections Set.univ).piece j) :
    (actualSectionDuality cs b basis).pairing m n ∈
      polynomialGrading ℝ σ (i+j-(cs.length b : ℤ)) :=
  (actualSymmetricPairing cs b basis).homogeneous i j m n
    (fun x => hm x (Set.mem_univ x)) (fun x => hn x (Set.mem_univ x))

end
end KLInvariance.BruhatGraph

end


section

/-! Exact numerical endpoints for the actual sheaf, conditional on the two
explicit genuine normalization inputs. These implications are NOT a proof of
existence of the pairing or the Kazhdan--Lusztig character theorem. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 theorem emptyKernel_hilbert (x : Interval cs u b) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.sheaf.kernelHilbert q x ∅ =
      Polynomial.eval₂ (Int.castRingHom ℝ) q (stalkCharacter cs u b basis hub x) *
        (1-q)⁻¹ ^ Fintype.card σ := by
  let _ := B.free x
  let c := (exists_nonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg).some
  have he : B.sheaf.upwardSubmodule x ∅ = ⊤ := by
    ext v
    change (∀ e, e ∈ (∅ : Set (Sheaf.Outgoing (G := graph cs u b) x)) → _) ↔ True
    simp
  rw [GradedSheaf.kernelHilbert,he,Submodule.restrictScalars_top,
    stalkCharacter_eq_character cs u b basis hub B x,
    character_eq (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg c]
  simpa only [Hilbert.value,Hilbert.term_top] using (c.hasSum hq hq1).tsum_eq

end
end KLInvariance.BruhatGraph

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
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)
noncomputable section

 omit [Fintype σ] in
 theorem restrictBoundary_kernel (x : Interval cs u b) (T : Set (Edge cs 1 b)) :
    (restrictBoundary cs u b basis hub B).sheaf.upwardSubmodule x
      {e | (upperInclusion cs u b).edge e.val ∈ T} =
    B.sheaf.upwardSubmodule ((upperInclusion cs u b).vertex x) {e | e.val ∈ T} := by
  exact B.sheaf.forget.pullback_kernel (upperInclusion cs u b) x T Set.univ
    (fun e he => False.elim (he (Set.mem_univ e)))
    (fun e _ he => upperInclusion_outgoing cs u b e x he)

 theorem normalizedKernel_restrictBoundary (x : Interval cs u b) (T : Set (Edge cs 1 b)) (t : ℝ) :
    normalizedKernel cs u b basis hub (restrictBoundary cs u b basis hub B) t x
      {e | (upperInclusion cs u b).edge e.val ∈ T} =
    normalizedKernel cs 1 b basis (one_bruhat cs b) B t
      ((upperInclusion cs u b).vertex x) {e | e.val ∈ T} := by
  unfold normalizedKernel GradedSheaf.kernelHilbert
  rw [restrictBoundary_kernel cs u b basis hub B x T]
  rfl

 theorem normalized_emptyKernel_restrictBoundary (x : Interval cs u b) (t : ℝ) :
    normalizedKernel cs u b basis hub (restrictBoundary cs u b basis hub B) t x ∅ =
    normalizedKernel cs 1 b basis (one_bruhat cs b) B t
      ((upperInclusion cs u b).vertex x) ∅ := by
  simpa only [Set.mem_empty_iff_false,Set.ofPred_false] using
    normalizedKernel_restrictBoundary cs u b basis hub B x ∅ t

 theorem normalized_fullKernel_restrictBoundary (x : Interval cs u b) (t : ℝ) :
    normalizedKernel cs u b basis hub (restrictBoundary cs u b basis hub B) t x Set.univ =
    normalizedKernel cs 1 b basis (one_bruhat cs b) B t
      ((upperInclusion cs u b).vertex x) Set.univ := by
  simpa only [Set.mem_univ,Set.ofPred_true] using
    normalizedKernel_restrictBoundary cs u b basis hub B x Set.univ t

end
end KLInvariance.BruhatGraph

end


section

/-! Exact identification of chronological suffix conditions with the
strictly-later root conditions used in the height-one edge-image proof.
Equal-label edges may be ordered arbitrarily and cause no extra incident
condition. -/
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths MomentGraph
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

local instance instDecidable_solutions_8_recb270_1 (p : Prop) : Decidable p := Classical.propDecidable p
omit [Fintype I] in
 theorem chronologicalSchedule_full (e : Edge cs u b) : e ∈ chronologicalSchedule φ :=
  List.mem_reverse.mpr (transportedSchedule_full φ e)

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

omit [Fintype I] [Fintype σ] in
 theorem schedule_all_conditions (x : Interval cs u b) :
    remainingConditions cs u b (chronologicalSchedule φ) x = Set.univ := by
  ext e
  simp only [remainingConditions,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact chronologicalSchedule_full φ e.val

end
end KLInvariance.BruhatGraph

end


section

/-! Native endpoint normalization from the ACTUAL stalk characters. Unlike the
KL-labelled endpoints, these need neither character recognition nor Hodge. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.actualInterval
attribute [local instance] OAI.KLInvariance.BruhatGraph.actualEdges
attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidableEq_solutions
theorem normalized_emptyKernel_scaledStalk (x : Interval cs 1 b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) (ActualBoundary cs b basis) t x ∅=
      scaledStalk cs b basis t x := by
  rw [normalizedKernel,emptyKernel_hilbert cs 1 b basis (one_bruhat cs b)
    (ActualBoundary cs b basis) x (sq_pos_of_pos ht) (by nlinarith)]
  dsimp only [stateScale,scaledStalk]
  have hne : 1-t^2≠0 := ne_of_gt (by nlinarith : 0<1-t^2)
  rw [inv_pow]
  field_simp [hne,inv_pow]

 theorem normalized_fullKernel_scaledStalk (x : Interval cs 1 b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) (ActualBoundary cs b basis) t x Set.univ=
      scaledStalk cs b basis t⁻¹ x := by
  let C := ActualBoundary cs b basis
  let := C.free x
  let c := (exists_nonnegativeBasis (σ := σ) (C.sheaf.vertex x).piece
    (C.sheaf.vertex x).nonneg).some
  have hcp : c.polynomial=stalkCharacter cs 1 b basis (one_bruhat cs b) x := by
    rw [stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) C x,
      character_eq (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg c]
  rw [normalizedKernel,GradedSheaf.kernelHilbert,
    fullKernel_eq cs 1 b basis (one_bruhat cs b) C x,
    costalk_hilbert_of_duality cs 1 b basis (one_bruhat cs b) C (actualSectionDuality cs b basis)
      (cs.length b) (actualSectionDuality_homogeneous cs b basis) x c
      (sq_pos_of_pos ht) (by nlinarith),hcp,incoming_card cs b x]
  dsimp only [stateScale,scaledStalk]
  have hscale : t^((cs.length x.val : ℤ)-cs.length b)*
      (t^2)^((cs.length b : ℤ)-cs.length x.val)=
      (t⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [show (t^2)^((cs.length b : ℤ)-cs.length x.val)=
      t^(2*((cs.length b : ℤ)-cs.length x.val)) by rw [zpow_mul]; norm_num,
      ←zpow_add₀ ht.ne',inv_zpow,←zpow_neg]
    congr 1
    omega
  rw [show (t^2)⁻¹=(t⁻¹)^2 by rw [inv_pow]]
  have hne : 1-t^2≠0 := ne_of_gt (by nlinarith : 0<1-t^2)
  calc
    _ = (t^((cs.length x.val : ℤ)-cs.length b)*
      (t^2)^((cs.length b : ℤ)-cs.length x.val))*
      eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x) := by
      have hcancel : (1-t^2)^(Fintype.card σ)*((1-t^2)⁻¹)^(Fintype.card σ)=1 := by
        rw [←mul_pow,mul_inv_cancel₀ hne,one_pow]
      calc
        _ = ((1-t^2)^(Fintype.card σ)*((1-t^2)⁻¹)^(Fintype.card σ))*
            ((t^((cs.length x.val : ℤ)-cs.length b)*(t^2)^((cs.length b : ℤ)-cs.length x.val))*
            eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)) := by ring
        _ = _ := by rw [hcancel,one_mul]
    _ = _ := by rw [hscale]

 theorem schedule_final_scaledStalk (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t [] x=
      scaledStalk cs b basis t ((upperInclusion cs a b).vertex x) := by
  have he : remainingConditions cs a b [] x=∅ := by
    ext e
    simp [remainingConditions]
  rw [scheduleState,he]
  unfold intervalBoundary
  rw [normalized_emptyKernel_restrictBoundary]
  exact normalized_emptyKernel_scaledStalk cs b basis _ ht ht1

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SimultaneousInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
R-first simultaneous invariance and transported-schedule terminal-kernel freeness: upper-interval freeness, lower-interval cancellation, reversal and endpoint bottom freeness; all-entry transport and KL degree rigidity.
-/


section

/-! Actual-character comparison: no identification with the KL basis is used.
This permits induction on R kernels rather than on stalk character recognition. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b)
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section

 local instance instDecidableEq_solutions_1_recb270_1 (X : Type*) : DecidableEq X := Classical.decEq X
theorem transported_initial_scaledStalk {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t (chronologicalSchedule φ) x=
      scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x) := by
  rw [scheduleState,schedule_all_conditions φ]
  unfold intervalBoundary
  rw [normalized_fullKernel_restrictBoundary]
  exact normalized_fullKernel_scaledStalk cs b basis _ ht ht1

 theorem actual_endpoint_of_rTilde_eq_oai
    (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t []=
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (scheduleState cs a b basis hab (intervalBoundary basis hab) t (chronologicalSchedule φ))
        (chronologicalSchedule φ).reverse := by
  rw [funext (schedule_final_scaledStalk cs b basis a hab ht ht1),
    funext (transported_initial_scaledStalk basis hab φ ht ht1),
    chronologicalSchedule,List.reverse_reverse]
  funext x
  rw [transported_dispatch_matrix φ _ (Int.castRingHom ℝ),
    scaledStalk_reciprocity_upper cs b basis t ht.ne' a x]
  congr 1
  funext z
  rw [hr x z]

end
end KLInvariance.BruhatGraph

end


end OAI
end

theorem solution.{u, u'} : type_of% @OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq_oai.{u, u'} := @OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq_oai.{u, u'}
