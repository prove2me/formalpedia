-- Prove2me | solution 1 for GlobalTheory.SqZero.expBij_of_unitInChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:17.88269+00:00
-- url     : https://prove2.me/submissions/dd49c942-b46c-4fee-8cb0-fedf2c68182a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_addDers_apply
import Theorems.Thm_GlobalTheory_SqZero_chart_inj
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_of_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_exists_ders
import Theorems.Thm_GlobalTheory_SqZero_ker_fst_sq
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_GlobalTheory_SqZero_lieExp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_smooth_of_chart
import Theorems.Thm_GlobalTheory_SqZero_vecTo_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_single
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
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
variable {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : ∀ i, IsTangent (v i)) (hS : UnitInChart G S)
    (h : IsLieBasisOver S v) (α : S →ₐ[R] A) : ExpBij A v := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hS
  have := smooth_of_chart j
  obtain ⟨κ, _, β, τ, hτ⟩ := exists_ders R B
  let E := TrivSqZeroExt S (Fin n → S)
  let e : Fin n → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨χ, hχ, hχu⟩ := exists_chart_of_mem_redKer j
    ((TrivSqZeroExt.inlAlgHom R S (Fin n → S)).comp u)
    (by rw [← spMap_comp, Category.assoc, hu, comp_one']) (ker_fst_sq (R := R) (S := S) (Fin n → S))
    (lieExp_mem_redKer hv e (fun i => rfl) fun i => he i i)
  have hχu' : ∀ b, (χ b).fst = u b := fun b => by
    simpa [RingHom.mem_ker, sub_eq_zero] using hχu b
  have F : ∀ {T : Type} [CommRing T] [Algebra R T] (θ : S →ₐ[R] T) (c : Fin n → T)
      (hc : ∀ i k, c i * c k = 0),
      lieExp v c (fun i => hc i i) = spMap ((vecTo θ c hc).comp χ) ≫ j := by
    intro T _ _ θ c hc
    rw [← spMap_comp, Category.assoc, ← hχ, comp_lieExp]
    exact lieExp_congr _ (fun i => (vecTo_single θ c hc i).symm) _ _
  have Finr : ∀ s : Fin n → S, tanExp v s = spMap ((vecTo (inlS R S) (fun i => inr (s i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ) ≫ j := fun s => F _ _ _
  have ha : ∀ i, ∃ a : Fin n → S, ∀ b, u (τ i b) = ∑ k, (χ b).snd k * a k := by
    intro i
    classical
    let t : κ → DualNumber S := fun k => inr (if k = i then 1 else 0)
    have ht : ∀ k l, t k * t l = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
    obtain ⟨a, ha⟩ := h.2 (spMap (addDers τ ((inlS R S).comp u) t ht) ≫ j) (by
      rw [IsTanOver, ← Category.assoc, spMap_comp, ← hu]
      congr 2
      ext b
      simp [addDers_apply, TrivSqZeroExt.fst_sum, t])
    rw [Finr] at ha
    refine ⟨a, fun b => ?_⟩
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (chart_inj j ha) b)
    simpa [addDers_apply, vecTo_apply, TrivSqZeroExt.snd_sum, t, mul_comm] using this
  choose a ha using ha
  have hX : ∀ b k, (χ b).snd k = ∑ i, u (τ i b) * (χ (β i)).snd k := by
    intro b k
    have := congrFun (congrArg TrivSqZeroExt.snd (hτ _ χ
      ((TrivSqZeroExt.inlAlgHom R S (Fin n → S)).comp u)
      (fun b b' => by ext <;> simp [hχu']) b)) k
    simpa [TrivSqZeroExt.snd_sum, hχu'] using this
  have hδ : ∀ k, (fun l => ∑ i, a i l * (χ (β i)).snd k) = Pi.single k 1 := by
    intro k
    refine h.1 _ _ ?_
    rw [Finr, Finr]
    congr 2
    refine AlgHom.ext fun b => TrivSqZeroExt.ext
      (by simp [vecTo_apply, TrivSqZeroExt.fst_sum]) ?_
    have : ∑ l, (χ b).snd l * ∑ i, a i l * (χ (β i)).snd k = (χ b).snd k := by
      rw [hX b k]
      simp only [ha, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    simpa [vecTo_apply, TrivSqZeroExt.snd_sum, Pi.single_apply, mul_comm] using this
  intro J hJ
  refine ⟨fun c c' hcJ hcJ' hc hc' hcc => ?_, fun y hy => ?_⟩
  · rw [F α c fun i k => mul_eq_zero_of_sq hJ (hcJ i) (hcJ k),
      F α c' fun i k => mul_eq_zero_of_sq hJ (hcJ' i) (hcJ' k)] at hcc
    have e₁ : ∀ b, ∑ k, α ((χ b).snd k) * c k = ∑ k, α ((χ b).snd k) * c' k := fun b => by
      simpa [vecTo_apply] using AlgHom.congr_fun (chart_inj j hcc) b
    have e₂ : ∀ (d : Fin n → A) l, d l = ∑ i, α (a i l) * ∑ k, α ((χ (β i)).snd k) * d k := by
      intro d l
      simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum]
      have : ∀ k, ∑ i, a i l * (χ (β i)).snd k = (Pi.single k 1 : Fin n → S) l :=
        fun k => congrFun (hδ k) l
      simp [this, Pi.single_apply, apply_ite]
    funext l
    rw [e₂ c l, e₂ c' l]
    simp only [e₁]
  · obtain ⟨φ, rfl, hφ⟩ := exists_chart_of_mem_redKer j (α.comp u)
      (by rw [← spMap_comp, Category.assoc, hu, comp_one']) hJ hy
    let c : Fin n → A := fun k => ∑ i, α (a i k) * (φ (β i) - α (u (β i)))
    have hcJ : ∀ k, c k ∈ J := fun k => sum_mem fun i _ => J.mul_mem_left _ (hφ _)
    refine ⟨c, fun k => mul_eq_zero_of_sq hJ (hcJ k) (hcJ k), hcJ, ?_⟩
    rw [F α c fun i k => mul_eq_zero_of_sq hJ (hcJ i) (hcJ k)]
    congr 2
    ext b
    have := hτ A φ (α.comp u) (fun b b' => mul_eq_zero_of_sq hJ (hφ b) (hφ b')) b
    rw [AlgHom.comp_apply, vecTo_apply, hχu', ← sub_eq_iff_eq_add']
    refine this.trans ?_
    simp only [AlgHom.comp_apply, ha, map_sum, map_mul, c, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm
end GlobalTheory.SqZero
