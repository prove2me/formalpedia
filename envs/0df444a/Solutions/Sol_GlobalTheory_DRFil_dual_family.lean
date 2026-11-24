-- Prove2me | solution 1 for GlobalTheory.DRFil.dual_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:21.098333+00:00
-- url     : https://prove2.me/submissions/a8a8091c-cacf-4881-8f47-90eac3b56c79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_left
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_right
import Theorems.Thm_GlobalTheory_DRFil_sm_self
import Theorems.Thm_GlobalTheory_DRFil_sm_mul
import Theorems.Thm_GlobalTheory_DRFil_sm_comm
import Theorems.Thm_GlobalTheory_DRFil_eq_sum_basis
import Theorems.Thm_GlobalTheory_DRFil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_act_bil
import Theorems.Thm_GlobalTheory_DRFil_act_sm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
namespace GlobalTheory.DRFil
theorem _root_.solution (ρ : Representation LL G V) (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq α]
    [DecidableEq ι] (v : Basis α LL V) (w : Basis α LL V') (hvw : ∀ a b, β (v a) (w b) = if a = b then 1 else 0)
    (e : LL ⊗[Qp] F) (he : e * e = e) (heG : ∀ g, actR PD LL g e = e) (d : ι → V ⊗[Qp] F)
    (hd : ∀ i, d i ∈ DdR PD ρ) (hed : ∀ i, sm Qp F LL V e (d i) = d i)
    (hind : ∀ r : ι → LL ⊗[Qp] F, ∑ i, sm Qp F LL V (r i) (d i) = 0 → ∀ i, e * r i = 0)
    (r : α → ι → LL ⊗[Qp] F)
    (hr : ∀ a, sm Qp F LL V e (v a ⊗ₜ[Qp] (1 : F)) = ∑ i, sm Qp F LL V (r a i) (d i))
    (d' : ι → V' ⊗[Qp] F)
    (hd' : ∀ i, d' i = sm Qp F LL V' e (∑ a, sm Qp F LL V' (r a i) (w a ⊗ₜ[Qp] (1 : F)))) :
    (∀ i, d' i ∈ DdR PD ρ') ∧ (∀ i j, bil Qp F β (d j) (d' i) = if j = i then e else 0) ∧
      ∀ y, sm Qp F LL V' e y = ∑ i, sm Qp F LL V' (bil Qp F β (d i) y) (d' i) := by
  have hv : ∀ a (x : V ⊗[Qp] F), bil Qp F β x (w a ⊗ₜ[Qp] (1 : F)) = ext Qp F (v.coord a) x := by
    intro a x
    have : ∀ x, β x (w a) = v.coord a x := fun x => by
      have h : β.flip (w a) = v.coord a := v.ext fun b => by
        simp [hvw, Finsupp.single_apply]
      exact LinearMap.congr_fun h x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul x b => simp [this]
  have hw : ∀ a (y : V' ⊗[Qp] F), bil Qp F β (v a ⊗ₜ[Qp] (1 : F)) y = ext Qp F (w.coord a) y := by
    intro a y
    have : ∀ y, β (v a) y = w.coord a y := fun y => by
      have h : β (v a) = w.coord a := w.ext fun b => by
        simp [hvw, Finsupp.single_apply, eq_comm]
      exact LinearMap.congr_fun h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x b => simp [this]
  have hx : ∀ x, sm Qp F LL V e x = ∑ i, sm Qp F LL V (bil Qp F β x (d' i)) (d i) := by
    intro x
    have h1 : ∀ i, bil Qp F β x (d' i) = e * ∑ a, ext Qp F (v.coord a) x * r a i := by
      intro i
      rw [hd', bil_sm_right, sm_self, map_sum]
      simp only [bil_sm_right, sm_self, hv, mul_comm]
    simp only [h1, sm_mul, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    conv_lhs => rw [eq_sum_basis v x, ← he, sm_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sm_comm e (ext Qp F (v.coord a) x), hr, map_sum, map_sum]
  have hed' : ∀ i, sm Qp F LL V' e (d' i) = d' i := fun i => by rw [hd', ← sm_mul, he]
  have hδ : ∀ i j, bil Qp F β (d j) (d' i) = if j = i then e else 0 := by
    intro i j
    have h := hind (fun i => bil Qp F β (d j) (d' i) - if j = i then 1 else 0) (by
      simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, ← hx, hed]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp) i
    rw [mul_sub, sub_eq_zero, ← sm_self, ← bil_sm_right, hed'] at h
    rw [h]
    split_ifs <;> simp
  have hz : ∀ z, sm Qp F LL V' e z = z → (∀ j, bil Qp F β (d j) z = 0) → z = 0 := by
    intro z hz h
    have : ∀ a, ext Qp F (w.coord a) z = 0 := by
      intro a
      rw [← hw, ← hz, bil_sm_right, ← bil_sm_left, hr, map_sum, LinearMap.sum_apply]
      simp [bil_sm_left, h]
    rw [eq_sum_basis w z]
    simp [this]
  refine ⟨fun i => (mem_DdR PD ρ' _).2 fun g => ?_, hδ, fun y => ?_⟩
  · rw [← sub_eq_zero]
    refine hz _ ?_ fun j => ?_
    · rw [map_sub, hed', ← heG g, ← act_sm, hed']
    · have h := act_bil PD ρ ρ' (Representation.trivial LL G LL) β (fun g v w => by simp [hβ]) g (d j) (d' i)
      rw [(mem_DdR PD ρ _).1 (hd j)] at h
      rw [map_sub, ← h, hδ]
      split_ifs
      · exact sub_eq_zero.2 (heG g)
      · simp
  · rw [← sub_eq_zero]
    refine hz _ ?_ fun j => ?_
    · rw [map_sub, ← sm_mul, he, map_sum]
      simp only [sm_comm e, hed']
    · rw [map_sub, map_sum]
      simp only [bil_sm_right, hδ, sm_self]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [mul_comm]
end GlobalTheory.DRFil
