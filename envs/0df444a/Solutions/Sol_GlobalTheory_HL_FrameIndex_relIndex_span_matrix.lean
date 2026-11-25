-- Prove2me | solution 1 for GlobalTheory.HL.FrameIndex.relIndex_span_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:30.888732+00:00
-- url     : https://prove2.me/submissions/986125f7-df0f-466e-b054-52f7904bcc5c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_LatDet_relVol_map
import Theorems.Thm_GlobalTheory_HL_LatDet_resQ_ne_zero
import Theorems.Thm_GlobalTheory_HL_TupleJac_exists_int_basis
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameIndex
namespace GlobalTheory.HL.FrameIndex
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m b hb A c hc0 hA Q Q' hQ hQ'
  obtain ⟨c2, hc, hN⟩ := TupleJac.exists_int_basis L
  have := L.free
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 c hc0
  have hAu : IsUnit A.det := by
    have h := (IsUnit.mk0 c hc0).map (algebraMap F E)
    rw [← hA] at h
    exact isUnit_of_mul_isUnit_left h
  have hdet : IsUnit (LinearMap.det (Matrix.toLin' A)) := by
    rw [LinearMap.det_toLin']; exact hAu
  set φ := LinearMap.equivOfIsUnitDet hdet with hφdef
  have hφ : φ.toLinearMap = Matrix.toLin' A := LinearMap.coe_equivOfIsUnitDet hdet
  have hφx : ∀ x, φ x = A.mulVec x := fun x => LinearMap.congr_fun hφ x
  let W0 : AddSubgroup (Fin m → E) := AddSubgroup.pi Set.univ fun _ => L.O.toAddSubgroup
  have hW0 : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp only [W0, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff, Subring.mem_toAddSubgroup]
  have h := LatDet.relVol_map ϖ hϖ (c2.smulTower (Pi.basisFun E (Fin m))) (φ.restrictScalars F)
    (vE L ϖ (algebraMap F E c)) u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hu, ← hA, ← hN, ← LinearMap.det_toLin', ← hφ, ← LinearMap.det_restrictScalars]
      rfl) W0 (by
      intro x
      simp only [hW0, hc, Module.Basis.smulTower_repr, Pi.basisFun_repr]
      exact ⟨fun h i => h _ _, fun h j i => h (i, j)⟩)
  let e : (Fin m → E) →+ (Fin n → E) := (Fintype.linearCombination E b).toAddMonoidHom
  have he : ∀ x, e x = ∑ i, x i • b i := fun x => Fintype.linearCombination_apply E b x
  have hei : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hb x ((he x).symm.trans hx))
  have h1 : Q.toAddSubgroup = W0.map e := by
    ext w
    rw [hQ, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun i => x i, (hW0 _).2 fun i => (x i).2, he _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fun i => ⟨x i, (hW0 _).1 hx i⟩, (he _).symm⟩
  have hsum : ∀ x : Fin m → E, e (φ x) = ∑ j, x j • ∑ i, A i j • b i := by
    intro x
    rw [he, hφx]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : Q'.toAddSubgroup =
      (W0.map (φ.restrictScalars F).toAddEquiv.toAddMonoidHom).map e := by
    ext w
    rw [hQ', Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨fun i => x i, (hW0 _).2 fun i => (x i).2, rfl⟩, hsum _⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨fun i => ⟨x i, (hW0 _).1 hx i⟩, (hsum _).symm⟩
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hei,
    AddSubgroup.relIndex_map_map_of_injective _ _ hei]
  obtain ⟨n1, n2, h3⟩ := h
  refine ⟨n1, n2, ?_⟩
  unfold relVol at h3
  have hq : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast LatDet.resQ_ne_zero hϖ
  rw [div_eq_iff (by exact_mod_cast n1)] at h3
  rw [h3, ← mul_assoc, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, one_mul]
end GlobalTheory.HL.FrameIndex
