-- Prove2me | solution 1 for GlobalTheory.TorusConst.val_unit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:48.468398+00:00
-- url     : https://prove2.me/submissions/01a7d9aa-de01-4147-bf62-c0ba44d97a85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_spm_val
import Theorems.Thm_GlobalTheory_TorusConst_val_val
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_GlobalTheory_TorusConst_exists_good
import Theorems.Thm_GlobalTheory_TorusConst_val_eq_of_affine
import Theorems.Thm_GlobalTheory_TorusConst_val_twist
import Theorems.Thm_GlobalTheory_TorusToProper_point_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
variable [GrpObj B] {L R : Type} [Field L] [Algebra K L] [CommRing R] [Algebra K R]
namespace GlobalTheory.TorusConst
theorem _root_.solution [IsSeparated B.hom] [IsDomain R] {b b' : sp K L[X] ⟶ B} (h : Glue b b')
    (i : L →ₐ[K] R) (t : Rˣ) (e : R →ₐ[K] L) (he : Function.Surjective e) (het : e t = 1) :
    val b i (t : R) = val b i 1 := by
  have het' : e (t⁻¹ : Rˣ) = 1 := by
    have := congrArg e t.mul_inv
    rwa [map_mul, het, _root_.one_mul, map_one] at this
  have hg : Glue (twist b i t) (twist b' i (t⁻¹ : Rˣ)) := by
    intro A _ _ c x hx
    have h1 : c t * c (t⁻¹ : Rˣ) = 1 := by rw [← map_mul, t.mul_inv, map_one]
    have h2 : c t ≠ 0 := left_ne_zero_of_mul_eq_one h1
    rw [val_twist, val_twist, h A _ _ (mul_ne_zero h2 hx), h A _ _ hx, mul_inv,
      eq_inv_of_mul_eq_one_right h1]
  let o : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨_, ⟨V, hV, rfl⟩, hoV, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (η[B].left o)) isOpen_univ
  have h1 : ∀ (b : sp K L[X] ⟶ B) (s : R), e s = 1 →
      ∀ q, (val (twist b i s) (CAlgHom.comp e) (X : L[X])).left q ∈ V := by
    intro b s hs q
    rw [val_twist, AlgHom.comp_apply, hs, map_one, _root_.one_mul, mul_inv_cancel, Hom.one_def]
    have : (toUnit (sp K L[X])).left q = o := Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
    change η[B].left ((toUnit (sp K L[X])).left q) ∈ V
    rw [this]
    exact hoV
  obtain ⟨g, hg1, hg2⟩ := exists_good hg V e he (h1 _ _ het) (h1 _ _ het')
  obtain ⟨g', hg1', hg2'⟩ := exists_good hg.symm V e he (h1 _ _ het') (h1 _ _ het)
  let E := FractionRing R
  let c : R →ₐ[K] E := IsScalarTower.toAlgHom K R E
  have hc : Function.Injective c := IsFractionRing.injective R E
  have hne : ∀ r, e r ≠ 0 → c r ≠ 0 := fun r hr h0 =>
    hr (by rw [hc (h0.trans (map_zero c).symm), map_zero])
  have hcomp : ∀ (A : Type) [CommRing A] [Algebra K A] (d : E →ₐ[K] A) (x : A),
      (aevalTower d x).comp (CAlgHom.comp c) = d.comp c := by
    intro A _ _ d x
    ext a
    simp
  have hg' : Glue (val (twist b i t) (CAlgHom.comp c) (X : E[X]))
      (val (twist b' i (t⁻¹ : Rˣ)) (CAlgHom.comp c) (X : E[X])) := by
    intro A _ _ d x hx
    rw [val_val, val_val, hcomp, hcomp, aevalTower_X, aevalTower_X, hg A _ _ hx]
  have key := val_eq_of_affine hg' V hV (hg2 E c (hne _ hg1)) (hg2' E c (hne _ hg1')) 1 0
  rw [val_val, val_val, hcomp, hcomp, aevalTower_X, aevalTower_X, val_twist, val_twist,
    mul_zero, mul_inv_cancel, _root_.mul_one, mul_inv_eq_one] at key
  apply point_ext c hc
  rw [spm_val, spm_val, map_one]
  exact key
end GlobalTheory.TorusConst
