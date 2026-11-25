-- Prove2me | solution 1 for GlobalTheory.FrameOver.card_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:50.697422+00:00
-- url     : https://prove2.me/submissions/3f340592-15d5-46a3-bf77-c2dbbc941180

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Theorems.Thm_GlobalTheory_FrameOver_card_coker_dvr
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_add_mul
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameOver
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι L.O) (a : ℕ)
    (u : (𝒪[F])ˣ) (hN : ((N.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    Nat.card ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) = resQ ϖ ^ (2 * a) := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hal : ∀ a : 𝒪[F], ((algebraMap 𝒪[F] L.O a : L.O) : E) = algebraMap F E a := fun _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => GlobalTheory.UnramOrder.cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  have hbase : ∀ r, c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r := fun r =>
    Subtype.ext (by rw [hcv, hal, AlgEquiv.commutes])
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (GlobalTheory.UnramOrder.algebraMap_inj L (congrArg Subtype.val h))
  have hu : IsUnit ((⟨ω, hω⟩ : L.O) - c ⟨ω, hω⟩) :=
    IsUnit.of_mul_eq_one ⟨e, he⟩ (Subtype.ext hωe)
  have hli : LinearIndependent 𝒪[F] ![(1 : L.O), ⟨ω, hω⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
    have h' := congrArg c h
    rw [map_add, map_mul, hbase, hbase, map_zero] at h'
    have hb : algebraMap 𝒪[F] L.O b = 0 :=
      hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap 𝒪[F] L.O a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  have hsp : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ⟨ω, hω⟩]) := by
    intro x _
    obtain ⟨a, b, h⟩ := GlobalTheory.UnramOrder.exists_eq_add_mul c hc hbase hfix hu x
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨![a, b], by simp [h, Algebra.smul_def]⟩
  let B := Module.Basis.mk hli hsp
  have : Module.Free 𝒪[F] L.O := Module.Free.of_basis B
  have : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis B
  have hdet : N.det = algebraMap 𝒪[F] L.O (ϖ ^ a * u) := Subtype.ext (by rw [hN, hal]; simp)
  have key := card_coker_dvr hϖ (N.vecMulLinear.restrictScalars 𝒪[F]) (2 * a) (by
    have h1 : LinearMap.det N.vecMulLinear = N.det := by
      rw [← Matrix.det_transpose, ← LinearMap.det_toLin']
      congr 1
      refine LinearMap.ext fun x => ?_
      simp [Matrix.mulVec_transpose]
    rw [LinearMap.det_restrictScalars, h1, hdet, Algebra.norm_algebraMap_of_basis B,
      Fintype.card_fin, mul_pow, ← pow_mul, mul_comm a 2]
    exact associated_mul_unit_left _ _ (u.isUnit.pow 2))
  rw [resQ, ← key]
  rfl
end GlobalTheory.FrameOver
