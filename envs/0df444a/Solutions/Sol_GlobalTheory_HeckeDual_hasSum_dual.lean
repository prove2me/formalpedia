-- Prove2me | solution 1 for GlobalTheory.HeckeDual.hasSum_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:31.288524+00:00
-- url     : https://prove2.me/submissions/e191386a-7c0f-4117-814d-09b6ca2cd2e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_HeckeSeries_hasSum_integral_cosets
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_nabs_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LGrp_nabs_eq_zpow
import Theorems.Thm_GlobalTheory_SatakeFlip_cosetMap_cosetMap
import Theorems.Thm_GlobalTheory_SatakeFlip_cosetMap_mk
import Theorems.Thm_GlobalTheory_SatakeFlip_invRevT_invRevT
import Theorems.Thm_GlobalTheory_SatakeFlip_invRevT_mem_borel
import Theorems.Thm_GlobalTheory_SatakeFlip_inv_diag_mul
import Theorems.Thm_GlobalTheory_SatakeFlip_ord_inv_eq_neg
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
namespace GlobalTheory.HeckeDual
open GlobalTheory.SatakeFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma isBorelSph_comp_invRevT {γ : Fin n → ℂ}
    {φ : GL (Fin n) k → ℂ} (hφ : _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ) :
    _root_.GlobalTheory.SatakeBound.IsBorelSph k (fun i => (γ i.rev)⁻¹)
      (fun g => φ (_root_.GlobalTheory.SatakeFlip.invRevT g)) := by
  obtain ⟨hK, hB⟩ := hφ
  refine ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩
  · show φ (_root_.GlobalTheory.SatakeFlip.invRevT (g * x)) = φ (_root_.GlobalTheory.SatakeFlip.invRevT g)
    rw [map_mul]
    exact hK _ _ (_root_.GlobalTheory.SatakeFlip.invRevT_mem_KO hx)
  · have hb' := _root_.GlobalTheory.SatakeFlip.invRevT_mem_borel hb
    show φ (_root_.GlobalTheory.SatakeFlip.invRevT b) = _
    rw [hB _ hb' (fun i => (t i.rev)⁻¹) ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp [_root_.GlobalTheory.SatakeFlip.ord_inv_eq_neg, zpow_neg, inv_zpow]
    · intro i
      rw [_root_.GlobalTheory.SatakeFlip.invRevT_apply]
      have hi := _root_.GlobalTheory.SatakeFlip.inv_diag_mul hb i.rev
      rw [ht] at hi
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hi
open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma exists_cosetMap_out_eq_invRevT_mul
    (c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
      (_root_.GlobalTheory.SatakeFlip.cosetMap c).out = _root_.GlobalTheory.SatakeFlip.invRevT c.out * x := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
    (_root_.GlobalTheory.SatakeFlip.invRevT c.out)
  refine ⟨x, x.2, ?_⟩
  rw [← hx, ← _root_.GlobalTheory.SatakeFlip.cosetMap_mk, QuotientGroup.out_eq']
open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma mul_entries_integral {g h : GL (Fin n) k}
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k])
    (hh : ∀ i j, (h : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]) :
    ∀ i j, ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hg i l) (hh l j)
open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma invRevT_entries_integral_iff_inv (g : GL (Fin n) k) :
    (∀ i j, ((_root_.GlobalTheory.SatakeFlip.invRevT g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈
      𝒪[k]) ↔ ∀ i j, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  simp only [_root_.GlobalTheory.SatakeFlip.invRevT_apply]
  constructor
  · intro h i j
    simpa using h j.rev i.rev
  · intro h i j
    exact h _ _
open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma det_invRevT' (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeFlip.invRevT g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det ((↑g⁻¹ : Matrix (Fin n) (Fin n) k).transpose.submatrix Fin.rev Fin.rev) = _
  exact (Matrix.det_submatrix_equiv_self Fin.revPerm _).trans (Matrix.det_transpose _)
open MeasureTheory ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} in
private lemma ord_det_eq_zero_of_mem_KO {x : GL (Fin n) k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det x) = 0 := by
  have h := _root_.GlobalTheory.GLDoubling.nabs_det_of_mem_KO hx
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow] at h
  have hq : (1 : ℝ) < _root_.GlobalTheory.SplitWeil.resCard k := by
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  have := zpow_right_injective₀ (by positivity) hq.ne' (h.trans (zpow_zero _).symm)
  simpa using this
end GlobalTheory.HeckeDual
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.HeckeDual
open GlobalTheory.SatakeFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
open MeasureTheory ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}
namespace GlobalTheory.HeckeDual
namespace _root_.GlobalTheory.HeckeDual
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (-_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  intro k _ _ _ _ n γ φ hφ _ X hX
  have hrev : ∀ i : Fin n, (i.rev : ℕ) = n - 1 - i := fun i => by rw [Fin.val_rev]; omega
  have hX' : ∀ i : Fin n,
      ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (γ i.rev)⁻¹ * X‖ < 1 := by
    intro i
    have hi := hX i.rev
    rwa [hrev] at hi
  have H := _root_.GlobalTheory.HeckeSeries.hasSum_integral_cosets k n _ _
    (isBorelSph_comp_invRevT hφ) X hX'
  have hprod : ∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) *
      (γ i.rev)⁻¹ * X)⁻¹ =
      ∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹ :=
    Fintype.prod_equiv Fin.revPerm _ _ fun i => by rw [Fin.revPerm_apply, hrev]
  rw [hprod] at H
  let e : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} ≃
      {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    { toFun := fun c => ⟨_root_.GlobalTheory.SatakeFlip.cosetMap c.1, by
        obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
        rw [hc]
        exact mul_entries_integral
          ((invRevT_entries_integral_iff_inv _).mpr c.2)
          ((_root_.GlobalTheory.SplitFlip.mem_KO_iff x).mp hx).1⟩
      invFun := fun c => ⟨_root_.GlobalTheory.SatakeFlip.cosetMap c.1, by
        obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
        rw [hc, mul_inv_rev, ← map_inv]
        refine mul_entries_integral ((_root_.GlobalTheory.SplitFlip.mem_KO_iff x).mp hx).2 ?_
        refine (invRevT_entries_integral_iff_inv _).mpr ?_
        simpa using c.2⟩
      left_inv := fun c => Subtype.ext (_root_.GlobalTheory.SatakeFlip.cosetMap_cosetMap c.1)
      right_inv := fun c => Subtype.ext (_root_.GlobalTheory.SatakeFlip.cosetMap_cosetMap c.1) }
  convert e.hasSum_iff.mpr H using 1
  funext c
  obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
  show _ = X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det
      (_root_.GlobalTheory.SatakeFlip.cosetMap c.1).out)).toNat *
    φ (_root_.GlobalTheory.SatakeFlip.invRevT (_root_.GlobalTheory.SatakeFlip.cosetMap c.1).out)
  rw [hc, map_mul _root_.GlobalTheory.SatakeFlip.invRevT, _root_.GlobalTheory.SatakeFlip.invRevT_invRevT,
    hφ.1 _ _ (_root_.GlobalTheory.SatakeFlip.invRevT_mem_KO hx), map_mul,
    _root_.GlobalTheory.SmGL.ord_mul, det_invRevT', _root_.GlobalTheory.SatakeFlip.ord_inv_eq_neg,
    ord_det_eq_zero_of_mem_KO hx, add_zero]
end _root_.GlobalTheory.HeckeDual
end GlobalTheory.HeckeDual
