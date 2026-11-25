-- Prove2me | solution 1 for GlobalTheory.ChartJet.exists_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:28:16.270611+00:00
-- url     : https://prove2.me/submissions/42a23941-f50a-4f19-8630-8fa5fcc10273

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_ac_val
import Theorems.Thm_GlobalTheory_ChartJet_op_val
import Theorems.Thm_GlobalTheory_ChartJet_ptJ_sq
import Theorems.Thm_GlobalTheory_ChartJet_ptJ_aug
import Theorems.Thm_GlobalTheory_ChartJet_ptJ_trunc
import Theorems.Thm_GlobalTheory_ChartJet_ptJ_inj
import Theorems.Thm_GlobalTheory_ChartJet_exists_ptJ
import Theorems.Thm_GlobalTheory_ChartJet_ptJ_zero
import Theorems.Thm_GlobalTheory_FormalLog_pt_apply
import Theorems.Thm_GlobalTheory_SqZero_IsLiftAlong_mul
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
variable {x} (hx : IsUnivChart G d x)
include hx
namespace GlobalTheory.ChartJet
theorem _root_.solution [IsCommMonObj G] {O : Type} [CommRing O] (a : Geo.Tor.OAct O G) :
    ∃ (F : FGLaw R d) (A : OAct O F),
      (∀ m, ptJ x m (⟨F.F, F.const⟩ : Q R d 2) = ptJ x m (gen 0) * ptJ x m (gen 1)) ∧
      ∀ c m, ptJ x m (⟨A.act c, A.const c⟩ : Q R d 1) = ptJ x m (gen 0) ≫ a.act c := by
  obtain ⟨F0, hF0⟩ : ∃ F0 : Q R d 2, ∀ m, ptJ x m F0 = ptJ x m (gen 0) * ptJ x m (gen 1) :=
    exists_ptJ hx (fun m => ptJ x m (gen 0) * ptJ x m (gen 1))
      (fun m => by rw [MonObj.comp_mul, ptJ_aug hx, ptJ_aug hx, _root_.one_mul])
      (fun m => by rw [MonObj.comp_mul, ptJ_trunc hx, ptJ_trunc hx])
  have hA : ∀ c : O, ∃ A0 : Q R d 1, ∀ m, ptJ x m A0 = ptJ x m (gen 0) ≫ a.act c := by
    intro c
    have := a.hom c
    exact exists_ptJ hx (fun m => ptJ x m (gen 0) ≫ a.act c)
      (fun m => by rw [← Category.assoc, ptJ_aug hx, MonObj.one_comp])
      (fun m => by rw [← Category.assoc, ptJ_trunc hx])
  choose A0 hA0 using hA
  have hop : ∀ {l : ℕ} (u v : Q R d l) (m : ℕ), ptJ x m (op F0 u v) = ptJ x m u * ptJ x m v := by
    intro l u v m
    show ptJ x m (sq ![u, v] F0) = _
    rw [← ptJ_sq x m ![u, v] F0, hF0, MonObj.comp_mul, ptJ_sq, ptJ_sq, sq_gen, sq_gen]
    rfl
  have hac : ∀ {l : ℕ} (u : Q R d l) (c : O) (m : ℕ), ptJ x m (ac (A0 c) u) = ptJ x m u ≫ a.act c := by
    intro l u c m
    show ptJ x m (sq ![u] (A0 c)) = _
    rw [← ptJ_sq x m ![u] (A0 c), hA0, ← Category.assoc, ptJ_sq, sq_gen]
    rfl
  refine ⟨⟨F0.1, F0.2, ?unit, ?comm, ?assoc⟩,
    ⟨fun c => (A0 c).1, fun c => (A0 c).2, ?hom, ?add, ?mul, ?one⟩, fun m => hF0 m, fun c m => hA0 c m⟩
  case unit =>
    intro i
    have E : op F0 (0 : Q R d 1) (gen 0) = (gen 0 : Q R d 1) :=
      ptJ_inj hx fun m => by rw [hop, ptJ_zero hx, _root_.one_mul]
    have h := congrFun (op_val F0 (0 : Q R d 1) (gen 0)) i
    rw [E] at h
    exact h.symm.trans (pt_apply _ _)
  case comm =>
    intro i
    have E : op F0 (gen 1 : Q R d 2) (gen 0) = F0 :=
      ptJ_inj hx fun m => by rw [hop, hF0, _root_.mul_comm]
    have h := congrFun (op_val F0 (gen 1 : Q R d 2) (gen 0)) i
    rw [E] at h
    exact h.symm
  case assoc =>
    intro i
    have E : op F0 (op F0 (gen 0 : Q R d 3) (gen 1)) (gen 2) = op F0 (gen 0) (op F0 (gen 1) (gen 2)) :=
      ptJ_inj hx fun m => by simp only [hop, _root_.mul_assoc]
    have h := congrArg (fun r : Q R d 3 => r.1 i) E
    simp only [op_val] at h
    exact h
  case hom =>
    intro c
    have := a.hom c
    have E : ac (A0 c) (op F0 (gen 0 : Q R d 2) (gen 1)) = op F0 (ac (A0 c) (gen 0)) (ac (A0 c) (gen 1)) :=
      ptJ_inj hx fun m => by simp only [hac, hop, MonObj.mul_comp]
    have h := congrArg Subtype.val E
    simp only [ac_val, op_val] at h
    exact h
  case add =>
    intro c₁ c₂
    have E : A0 (c₁ + c₂) = op F0 (A0 c₁) (A0 c₂) :=
      ptJ_inj hx fun m => by rw [hA0, hop, hA0, hA0, a.add, MonObj.comp_mul]
    have h := congrArg Subtype.val E
    rw [op_val] at h
    exact h
  case mul =>
    intro c₁ c₂
    have E : A0 (c₁ * c₂) = ac (A0 c₁) (A0 c₂) :=
      ptJ_inj hx fun m => by rw [hA0, hac, hA0, Category.assoc, ← a.mul c₂ c₁, _root_.mul_comm c₂ c₁]
    have h := congrArg Subtype.val E
    rw [ac_val] at h
    exact h
  case one =>
    have E : A0 1 = (gen 0 : Q R d 1) :=
      ptJ_inj hx fun m => by rw [hA0, a.one, Category.comp_id]
    exact congrArg Subtype.val E
end GlobalTheory.ChartJet
