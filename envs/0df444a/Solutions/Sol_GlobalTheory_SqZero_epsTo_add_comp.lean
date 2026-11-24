-- Prove2me | solution 1 for GlobalTheory.SqZero.epsTo_add_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:38.573572+00:00
-- url     : https://prove2.me/submissions/6ec65dff-9e85-4218-80e8-e7cc90221e00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_comp_epsTo
import Theorems.Thm_GlobalTheory_SqZero_vecTo_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_single
import Theorems.Thm_GlobalTheory_SqZero_ker_fst_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_redKer_ext
import Theorems.Thm_GlobalTheory_SqZero_epsTo_zero_comp
import Theorems.Thm_GlobalTheory_SqZero_epsTo_comp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {A A' A₀ : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  [CommRing A₀] [Algebra R A₀]
variable {G}
namespace GlobalTheory.SqZero
theorem _root_.solution {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (t₁ t₂ : A)
    (h₁ : t₁ * t₁ = 0) (h₂ : t₂ * t₂ = 0) (h₁₂ : t₁ * t₂ = 0) (h : (t₁ + t₂) * (t₁ + t₂) = 0) :
    spMap (epsTo R (t₁ + t₂) h) ≫ w =
      (spMap (epsTo R t₁ h₁) ≫ w) * (spMap (epsTo R t₂ h₂) ≫ w) := by
  let E := TrivSqZeroExt R (Fin 2 → R)
  let e : Fin 2 → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  have he' : (e 0 + e 1) * (e 0 + e 1) = 0 := by simp [add_mul, mul_add, he]
  have hk : ∀ i, e i ∈ RingHom.ker (TrivSqZeroExt.fstHom R R (Fin 2 → R)) := fun i => rfl
  have ax : ∀ i : Fin 2, ∀ a b : Fin 2, (Pi.single i DualNumber.eps : Fin 2 → DualNumber R) a *
      (Pi.single i DualNumber.eps : Fin 2 → DualNumber R) b = 0 := by
    intro i a b
    simp only [Pi.single_apply]
    split_ifs <;> simp
  let q : Fin 2 → (E →ₐ[R] DualNumber R) := fun i =>
    vecTo (Algebra.ofId R _) (Pi.single i DualNumber.eps) (ax i)
  have hq : ∀ i a, q i (e a) = (Pi.single i DualNumber.eps : Fin 2 → DualNumber R) a :=
    fun i a => vecTo_single _ _ _ _
  have univ : spMap (epsTo R (e 0 + e 1) he') ≫ w =
      (spMap (epsTo R (e 0) (he 0 0)) ≫ w) * (spMap (epsTo R (e 1) (he 1 1)) ≫ w) := by
    refine redKer_ext (ker_fst_sq (R := R) (S := R) (Fin 2 → R))
      (epsTo_comp_mem_redKer hw (add_mem (hk 0) (hk 1)) _)
      (mul_mem (epsTo_comp_mem_redKer hw (hk 0) _) (epsTo_comp_mem_redKer hw (hk 1) _))
      (q 0) (q 1) ?_ ?_ ?_
    · intro a h0 h1
      have a0 := congrArg TrivSqZeroExt.fst h0
      have a1 := congrArg TrivSqZeroExt.snd h0
      have a2 := congrArg TrivSqZeroExt.snd h1
      simp [q, vecTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl] at a0 a1 a2
      refine TrivSqZeroExt.ext a0 (funext fun i => ?_)
      fin_cases i
      · exact a1
      · exact a2
    · simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_epsTo]
      rw [epsTo_zero_comp hw (q 0 (e 1)) (by simp [hq]), mul_one]
      congr 3
      simp [hq]
    · simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_epsTo]
      rw [epsTo_zero_comp hw (q 1 (e 0)) (by simp [hq]), one_mul]
      congr 3
      simp [hq]
  let ψ : E →ₐ[R] A := vecTo (Algebra.ofId R A) ![t₁, t₂] (fun a b => by
    fin_cases a <;> fin_cases b <;> simp [h₁, h₂, h₁₂, mul_comm t₂ t₁])
  have hψ₀ : ψ (e 0) = t₁ := vecTo_single _ _ _ _
  have hψ₁ : ψ (e 1) = t₂ := vecTo_single _ _ _ _
  have := congrArg (spMap ψ ≫ ·) univ
  simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_epsTo, map_add, hψ₀, hψ₁] at this
  exact this
end GlobalTheory.SqZero
