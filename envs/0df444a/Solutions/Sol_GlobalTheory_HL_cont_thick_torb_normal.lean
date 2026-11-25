-- Prove2me | solution 1 for GlobalTheory.HL.cont_thick_torb_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:22.741392+00:00
-- url     : https://prove2.me/submissions/4498476f-21a5-4f2a-97d8-dc519e175afa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroup
import Theorems.Thm_GlobalTheory_HL_ThickSplit_cont_iUnion_cosets
import Theorems.Thm_GlobalTheory_HL_ThickSplit_rmul_rmul
import Theorems.Thm_GlobalTheory_HL_ThickSplit_rmul_one
import Theorems.Thm_GlobalTheory_HL_ThickSplit_map_rmul
import Theorems.Thm_GlobalTheory_HL_ThickSplit_gramT_rmul
import Theorems.Thm_GlobalTheory_HL_ThickSplit_mem_fixG
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CardQuotientPow_main
import Theorems.Thm_GlobalTheory_HL_ContModel_gramT_rmul
import Theorems.Thm_GlobalTheory_QuotientCardinality_main
import Theorems.Thm_GlobalTheory_T_matrixCongruentOneModUniformizerPow_group_and_orbits
import Theorems.Thm_GlobalTheory_T_tuple_jacobian_rightMul_isometry
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
open GlobalTheory.HL.ThickSplit
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x _ K K' hK hK' hnorm hidx i hi hstab hco
  obtain ⟨-, hgrp, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  have hjac := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λs hΛ m).2
  have hconj : ∀ a ∈ K, ∀ k ∈ K', a * k * a⁻¹ ∈ K' := by
    intro a ha k hk
    rw [← hnorm a ha]
    exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj a) K' hk
  haveI : (K'.subgroupOf K).Normal :=
    ⟨fun k hk a => hconj a a.2 k hk⟩
  set Fx := fixG L Hm (Submodule.span E (Set.range x)) with hFx
  have hsub : ∀ a b : K, a⁻¹ * b ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K →
      (fun x c => (b : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i ⊆
      (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i := by
    intro a b hab
    obtain ⟨k, hk, h, hh, hkh⟩ := Subgroup.mem_sup_of_normal_left.1 hab
    have hb : b = a * (k * h) := by rw [hkh]; group
    have hhx := ((mem_fixG L Hm x h).1 hh).2
    rintro _ ⟨_, ⟨_, ⟨k1, hk1, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨k * (h * k1 * (h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹),
      K'.mul_mem hk (hconj h h.2 k1 hk1), rfl⟩, A, hA, rfl⟩, ?_⟩
    simp only [map_rmul]
    congr 1
    funext c
    have : ((h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹) (x c) = x c := by
      conv_lhs => rw [← hhx c]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hb]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, this]
  have main := cont_iUnion_cosets (tupLat L Λs m) (K'.subgroupOf K) (Fx.subgroupOf K) hidx
    (fun a : K => (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i)
    (cont (tupLat L Λs m) (thick L ϖ (torb K' x) i))
    (fun a => (hjac a (hK a.2) _ hco).1) (fun a => (hjac a (hK a.2) _ hco).2)
    (fun a b hab => Set.Subset.antisymm
      (hsub b a (by simpa using Subgroup.inv_mem _ hab)) (hsub a b hab)) ?_
  · have hU : thick L ϖ (torb K x) i = ⋃ a : K, (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) ''
        thick L ϖ (torb K' x) i := by
      ext w
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, A, hA, rfl⟩
        exact ⟨⟨a, ha⟩, _, ⟨x, ⟨1, K'.one_mem, rfl⟩, A, hA, rfl⟩, map_rmul a x A⟩
      · rintro ⟨a, _, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
        exact ⟨_, ⟨a * k, K.mul_mem a.2 (hK' hk), rfl⟩, A, hA, map_rmul _ _ A⟩
    have hI : (K'.subgroupOf K).relIndex (Fx.subgroupOf K) = (Fx ⊓ K').relIndex (Fx ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_right Fx K, Subgroup.relIndex_subgroupOf inf_le_right,
        ← Subgroup.inf_relIndex_right K' (Fx ⊓ K)]
      congr 1
      rw [inf_comm, inf_assoc, inf_eq_right.2 hK']
    rw [hU, ← hI]
    exact main
  · intro a b hab
    obtain ⟨w, ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨k', hk', rfl⟩, A', hA', rfl⟩, hw⟩⟩ :=
      Set.not_disjoint_iff.1 hab
    obtain ⟨-, hdet, -, hinv, -, -⟩ := hgrp A' hA'
    have hB : A * A'⁻¹ ∈ congK L ϖ m i := (hgrp A hA).2.2.2.2.1 _ hinv
    set g : (Fin n → E) ≃ₗ[E] (Fin n → E) := k⁻¹ * (a : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹ * b * k' with hg
    have hgK : g ∈ K := K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hK' hk)) (K.inv_mem a.2)) b.2) (hK' hk')
    have h1 : rmul (fun c => g (x c)) A' = rmul x A := by
      rw [← map_rmul]
      funext c
      have h2 := congrFun hw c
      have h3 := congrFun (map_rmul k' x A') c
      have h4 := congrFun (map_rmul k x A) c
      simp only at h2 h3 h4
      rw [← h3, ← h4] at h2
      rw [hg]
      simp only [LinearEquiv.mul_apply]
      rw [h2]
      simp [LinearEquiv.coe_inv]
    have h2 : (fun c => g (x c)) = rmul x (A * A'⁻¹) := by
      rw [← rmul_rmul, ← h1, rmul_rmul, Matrix.mul_nonsing_inv _ hdet, rmul_one]
    have h3 : cT L (A * A'⁻¹) * gramT L Hm x * (A * A'⁻¹) = gramT L Hm x := by
      rw [← gramT_rmul, ← h2]
      ext c d
      exact hK hgK _ _
    obtain ⟨k'', hk'', h4⟩ := hstab x ⟨1, K'.one_mem, rfl⟩ _ hB h3
    rw [← h2] at h4
    have hfix : k''⁻¹ * g ∈ Fx := by
      refine (mem_fixG L Hm x _).2 ⟨hK (K.mul_mem (K.inv_mem (hK' hk'')) hgK), fun c => ?_⟩
      rw [LinearEquiv.mul_apply, congrFun h4 c]
      exact LinearEquiv.symm_apply_apply _ _
    have hmem : ∀ u (hu : u ∈ K'), (⟨u, hK' hu⟩ : K) ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K :=
      fun u hu => Subgroup.mem_sup_left hu
    have hmem' : (⟨k''⁻¹ * g, K.mul_mem (K.inv_mem (hK' hk'')) hgK⟩ : K) ∈
        K'.subgroupOf K ⊔ Fx.subgroupOf K := Subgroup.mem_sup_right hfix
    have hfin := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem k hk) (hmem k'' hk''))
      hmem') (Subgroup.inv_mem _ (hmem k' hk'))
    convert hfin using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group
end GlobalTheory.HL
