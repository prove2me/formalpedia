-- Prove2me | solution 1 for GlobalTheory.DiscOver.disc_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:24.815017+00:00
-- url     : https://prove2.me/submissions/b63d4216-2cbd-48c0-8ca9-498012e3ac9f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan
import Theorems.Thm_GlobalTheory_DiscOver_hf_sumr
import Theorems.Thm_GlobalTheory_DiscOver_gram_comb
import Theorems.Thm_GlobalTheory_DiscOver_det_cT
import Theorems.Thm_GlobalTheory_DiscOver_comb_comb
import Theorems.Thm_GlobalTheory_DiscOver_comb_one
import Theorems.Thm_GlobalTheory_DiscOver_sum_comb
import Theorems.Thm_GlobalTheory_DiscOver_li_of_gram
import Theorems.Thm_GlobalTheory_DiscOver_mem_spanO
import Theorems.Thm_GlobalTheory_DiscOver_dual_iff
import Theorems.Thm_GlobalTheory_DiscOver_det_mem
import Theorems.Thm_GlobalTheory_DiscOver_adj_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameIndex_relIndex_span_matrix
import Theorems.Thm_GlobalTheory_OrderBasis_order_basis
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DiscOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.DiscOver
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m : ℕ}
    (v : Fin m → Fin n → E) (c : F) (hc : c ≠ 0) (hG : (gram L Hm v).det = algebraMap F E c)
    (Mh Md : Submodule L.O (Fin n → E)) (h1 : Submodule.span L.O (Set.range v) ≤ Mh)
    (h2 : ∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v))
    (h3 : ∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O)
    (h4 : ∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) :
    0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup *
      ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 =
      resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧
      (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧
      ∃ b : Fin m → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  obtain ⟨-, hcj, -, hPIR, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨hadd, -, hpos, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hcu : IsUnit (algebraMap F E c) := (IsUnit.mk0 c hc).map _
  have hu : IsUnit (gram L Hm v).det := hG ▸ hcu
  have hv : ∀ a, v a ∈ Mh := fun a => h1 (Submodule.subset_span ⟨a, rfl⟩)
  have hle : Mh ≤ Submodule.span L.O (Set.range (comb v (gram L Hm v)⁻¹)) := fun x hx =>
    (dual_iff L Hm v hu x).1 ⟨h2 x hx, fun a => h3 x hx _ (hv a)⟩
  have hfg : Mh.FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have hsp : Submodule.span E (Mh : Set (Fin n → E)) = Submodule.span E (Set.range v) := by
    apply le_antisymm
    · exact Submodule.span_le.2 h2
    · apply Submodule.span_mono; rintro _ ⟨a, rfl⟩; exact hv a
  obtain ⟨b, hb, hMh⟩ := GlobalTheory.OrderBasis.order_basis L v (li_of_gram L Hm v hu) Mh hfg hsp
  have hbm : ∀ a, b a ∈ Mh := fun a => hMh ▸ Submodule.subset_span ⟨a, rfl⟩
  have hA : ∀ j, ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • b i = v j := fun j =>
    (mem_spanO L b _).1 (hMh ▸ hv j)
  choose s hs hsv using hA
  set A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => s j i with hAdef
  have hvA : v = comb b A := by funext j; exact (hsv j).symm
  have hdet : (gram L Hm b).det * (A.det * L.cj A.det) = algebraMap F E c := by
    rw [← hG, hvA, gram_comb, Matrix.det_mul, Matrix.det_mul, det_cT]; ring
  obtain ⟨-, -, cA, hcA⟩ := hcj A.det (det_mem _ A fun i j => hs j i)
  have hprod : IsUnit ((gram L Hm b).det * (A.det * L.cj A.det)) := hdet ▸ hcu
  have hub : IsUnit (gram L Hm b).det := isUnit_of_mul_isUnit_left hprod
  have hnt : Nontrivial E := by
    have := L.free
    exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcA0 : (cA : F) ≠ 0 := by
    intro h0
    have := isUnit_of_mul_isUnit_right hprod
    rw [hcA, h0, map_zero] at this
    exact not_isUnit_zero this
  set c0 : F := c / cA with hc0def
  have hc0 : c0 ≠ 0 := div_ne_zero hc hcA0
  have hcc : c = c0 * cA := by rw [hc0def]; field_simp
  have hdb : (gram L Hm b).det = algebraMap F E c0 := by
    have hAu : IsUnit (algebraMap F E cA) := (IsUnit.mk0 _ hcA0).map _
    apply hAu.mul_right_cancel
    rw [← map_mul, ← hcc, ← hdet, hcA]
  have hc0int : c0 ∈ 𝒪[F] := (hint c0).1
    (hdb ▸ det_mem _ _ fun i j => h3 _ (hbm j) _ (hbm i))
  have hv0 := (hpos c0 hc0).2 hc0int
  have hvA0 := (hpos cA hcA0).2 cA.2
  have hvc : vE L ϖ (algebraMap F E c) = vE L ϖ (algebraMap F E c0) + vE L ϖ (algebraMap F E cA) := by
    rw [← hadd c0 cA hc0 hcA0, ← hcc]
  have hspb : Submodule.span E (Set.range b) = Submodule.span E (Set.range v) := by
    rw [← hsp, hMh, Submodule.span_span_of_tower]
  have hMd : Md = Submodule.span L.O (Set.range (comb b (gram L Hm b)⁻¹)) := by
    ext x
    rw [h4, ← dual_iff L Hm b hub, hspb]
    refine and_congr_right fun _ => ⟨fun h a => h _ (hbm a), fun h y hy => ?_⟩
    obtain ⟨t, ht, rfl⟩ := (mem_spanO L b _).1 (hMh ▸ hy)
    rw [hf_sumr]
    exact L.O.sum_mem fun i _ => L.O.mul_mem (hcj _ (ht i)).1 (h i)
  have hbd : b = comb (comb b (gram L Hm b)⁻¹) (gram L Hm b) := by
    rw [comb_comb, Matrix.nonsing_inv_mul _ hub, comb_one]
  have hud : IsUnit (gram L Hm (comb b (gram L Hm b)⁻¹)).det := by
    rw [gram_comb, Matrix.mul_nonsing_inv _ hub, mul_one, det_cT]
    exact (Matrix.isUnit_nonsing_inv_det _ hub).map _
  have hMM : Mh ≤ Md := fun x hx => (h4 x).2 ⟨h2 x hx, h3 x hx⟩
  obtain ⟨-, -, e1⟩ := GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ b hb A cA hcA0 hcA Mh
    (Submodule.span L.O (Set.range v)) hMh (by rw [hvA]; rfl)
  obtain ⟨-, -, e2⟩ := GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ _ (li_of_gram L Hm _ hud) (gram L Hm b) (c0 * c0)
    (mul_ne_zero hc0 hc0) (by rw [hdb, AlgEquiv.commutes, map_mul]) Md Mh hMd
    (by rw [hMh]; exact congrArg (fun w => Submodule.span L.O (Set.range w)) hbd)
  rw [AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono h1)] at e1
  rw [AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono hMM), hadd c0 c0 hc0 hc0] at e2
  refine ⟨by omega, ?_, ?_, _, hMd⟩
  · obtain ⟨k0, hk0⟩ := Int.eq_ofNat_of_zero_le hv0
    obtain ⟨kA, hkA⟩ := Int.eq_ofNat_of_zero_le hvA0
    rw [hvc, hk0, hkA]
    rw [hkA] at e1
    rw [hk0] at e2
    have : ((k0 : ℤ) + kA).toNat = k0 + kA := by omega
    rw [this]
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [e1, e2, ← Nat.cast_add, zpow_natCast, zpow_natCast]
    push_cast
    ring
  · intro x hx
    have hx' := (dual_iff L Hm v hu x).1 ⟨((h4 x).1 hx).1, fun a => ((h4 x).1 hx).2 _ (hv a)⟩
    obtain ⟨t, ht, rfl⟩ := (mem_spanO L _ _).1 hx'
    have hadj : algebraMap F E c • (gram L Hm v)⁻¹ = (gram L Hm v).adjugate := by
      rw [← hG, Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hu, one_smul]
    rw [sum_comb, mem_spanO]
    refine ⟨(gram L Hm v).adjugate.mulVec t, fun i => ?_, ?_⟩
    · simp only [Matrix.mulVec, dotProduct]
      exact L.O.sum_mem fun j _ => L.O.mul_mem
        (adj_mem _ (gram L Hm v) (fun i j => h3 _ (hv j) _ (hv i)) i j) (ht j)
    · rw [← hadj, Matrix.smul_mulVec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; rfl
end GlobalTheory.DiscOver
