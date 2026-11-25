-- Prove2me | solution 1 for GlobalTheory.HL.Defect.defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:39.795745+00:00
-- url     : https://prove2.me/submissions/50e00142-f059-418d-9538-ffa81c1f3e90

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_HL_Defect_index_le_of_chars
import Theorems.Thm_GlobalTheory_HL_Defect_hf_comb
import Theorems.Thm_GlobalTheory_HL_Defect_hf_comb_r
import Theorems.Thm_GlobalTheory_HL_Defect_comb_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FiniteModuleOrder_card_eq_pow_and_index_ge
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_zero_l
import Theorems.Thm_GlobalTheory_T_card_cokernel_unramifiedOrder_matrix_of_det_base
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Defect
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : ι → Fin n → E) (a : ℕ) (u : (𝒪[F])ˣ)
    (hdet : (Matrix.of fun i j => hf L Hm (b i) (b j)).det =
      algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)))
    (N : Submodule L.O (Fin n → E)) (hMN : Submodule.span L.O (Set.range b) ≤ N)
    (hN : ∀ y ∈ N, y ∈ Submodule.span E (Set.range b))
    (hint : ∀ x ∈ N, ∀ y ∈ N, hf L Hm x y ∈ L.O) :
    (∀ y ∈ N, algebraMap F E ((ϖ : F) ^ a) • y ∈ Submodule.span L.O (Set.range b)) ∧
    ∃ i ≤ a, (Submodule.span L.O (Set.range b)).toAddSubgroup.relIndex N.toAddSubgroup =
      resQ ϖ ^ i := by
  have hb : ∀ i, b i ∈ N := fun i => hMN (Submodule.subset_span ⟨i, rfl⟩)
  set G : Matrix ι ι E := Matrix.of fun i j => hf L Hm (b i) (b j) with hG
  let A : Matrix ι ι L.O := Matrix.of fun i j => ⟨hf L Hm (b j) (b i), hint _ (hb j) _ (hb i)⟩
  have hAG : A.map L.O.subtype = Gᵀ := rfl
  have hAdet : ((A.det : L.O) : E) = G.det := by
    rw [← Matrix.det_transpose G, ← hAG]
    exact RingHom.map_det L.O.subtype A
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ((u : 𝒪[F]) : F) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hGu : IsUnit G.det := by
    rw [hdet]; exact (IsUnit.mk0 _ (mul_ne_zero (pow_ne_zero _ hϖ0) hu0)).map _
  choose co hco using fun y : N => (Submodule.mem_span_range_iff_exists_fun E).1 (hN y y.2)
  have hpair : ∀ (c : ι → E) j, hf L Hm (∑ i, c i • b i) (b j) = (Gᵀ *ᵥ c) j := fun c j => by
    rw [hf_comb]
    simp only [Matrix.mulVec, dotProduct, hG, Matrix.transpose_apply, Matrix.of_apply, mul_comm]
  let φ : N →+ (ι → L.O) :=
    { toFun := fun y j => ⟨hf L Hm y (b j), hint _ y.2 _ (hb j)⟩
      map_zero' := by funext j; exact Subtype.ext (hf_zero_l _ _ _)
      map_add' := fun x y => by funext j; exact Subtype.ext (hf_add_l _ _ _ _ _) }
  have hφ : ∀ y j, ((φ y j : L.O) : E) = (Gᵀ *ᵥ co y) j := fun y j => by
    rw [← hpair, hco]; rfl
  have hA : ∀ (c : ι → L.O) j, (((A *ᵥ c) j : L.O) : E) = (Gᵀ *ᵥ fun i => (c i : E)) j :=
    fun c j => RingHom.map_mulVec L.O.subtype A c j
  refine ⟨fun y hy => ?_, ?_⟩
  · have h1 : ∀ i, G.det * co ⟨y, hy⟩ i ∈ L.O := fun i => by
      have h2 : Gᵀ.adjugate *ᵥ (Gᵀ *ᵥ co ⟨y, hy⟩) = G.det • co ⟨y, hy⟩ := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.det_transpose]
      have h3 := RingHom.map_mulVec L.O.subtype A.adjugate (φ ⟨y, hy⟩) i
      have h4 : A.adjugate.map L.O.subtype = Gᵀ.adjugate := RingHom.map_adjugate L.O.subtype A
      have h5 : L.O.subtype ∘ φ ⟨y, hy⟩ = Gᵀ *ᵥ co ⟨y, hy⟩ := funext (hφ _)
      rw [h4, h5, h2] at h3
      have h6 : L.O.subtype ((A.adjugate *ᵥ φ ⟨y, hy⟩) i) ∈ L.O := Subtype.property _
      rwa [h3] at h6
    have h6 : y = ∑ i, co ⟨y, hy⟩ i • b i := (hco ⟨y, hy⟩).symm
    rw [h6, Finset.smul_sum]
    simp only [smul_smul]
    refine comb_mem L b _ fun i => ?_
    have h7 := L.O.mul_mem ((algebraMap_mem_iff L _).2 (u⁻¹ : (𝒪[F])ˣ).1.2) (h1 i)
    have h8 : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)) = (ϖ : F) ^ a := by
      rw [mul_left_comm, ← Subring.coe_mul, Units.inv_mul]; simp
    rwa [hdet, ← mul_assoc, ← map_mul, h8] at h7
  · set M := Submodule.span L.O (Set.range b) with hM
    let K : AddSubgroup (ι → L.O) := (LinearMap.range A.mulVecLin).toAddSubgroup
    have hK : K.index = resQ ϖ ^ (2 * a) := GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base L ϖ hϖ ι A a u (hAdet.trans hdet)
    have hq : 2 ≤ resQ ϖ := (order_facts L ϖ hϖ).2.2.2.2.2.2.1
    have hinj : Function.Injective Gᵀ.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2
        (by rwa [Matrix.det_transpose]))
    have hcomap : K.comap φ = M.toAddSubgroup.addSubgroupOf N.toAddSubgroup := by
      ext y
      constructor
      · rintro ⟨c, hc⟩
        have h1 : (fun i => (c i : E)) = co y := hinj (funext fun j => by
          rw [← hA, ← hφ, ← hc]; rfl)
        change (y : Fin n → E) ∈ M
        rw [← hco y, ← h1]
        exact comb_mem L b _ fun i => (c i).2
      · intro hy
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 (show (y : Fin n → E) ∈ M from hy)
        refine ⟨c, funext fun j => Subtype.ext ?_⟩
        rw [Matrix.mulVecLin_apply, hA, ← hpair]
        exact congrArg (fun v => hf L Hm v (b j)) hc
    have hle : K ≤ φ.range := by
      rintro _ ⟨c, rfl⟩
      refine ⟨⟨∑ i, (c i : E) • b i, hMN (comb_mem L b _ fun i => (c i).2)⟩,
        funext fun j => Subtype.ext ?_⟩
      rw [Matrix.mulVecLin_apply, hA, ← hpair]; rfl
    have hmul := AddSubgroup.relIndex_mul_index hle
    rw [← AddSubgroup.index_comap, hcomap, hK] at hmul
    have hne : resQ ϖ ^ (2 * a) ≠ 0 := pow_ne_zero _ (by omega)
    let β : N → (ι → L.O) →+ E := fun y =>
      { toFun := fun p => ∑ i, L.cj (co y i) * (p i : E)
        map_zero' := by simp
        map_add' := fun p p' => by simp [mul_add, Finset.sum_add_distrib] }
    have hO : ∀ x ∈ L.O, L.psi0 x = 1 := fun x hx => by
      simpa using (L.additive_character_dual_ring x).2 hx 1 L.O.one_mem
    have hidx := index_le_of_chars (M.toAddSubgroup.addSubgroupOf N.toAddSubgroup) φ.range
      (fun h => hne (by rw [← hmul, h, mul_zero])) (fun y => L.psi0.compAddMonoidHom (β y))
      (by
        rintro y _ ⟨x, rfl⟩
        apply hO
        have := hint _ x.2 _ y.2
        rwa [← hco y, hf_comb_r] at this)
      (by
        intro y y' h
        change ((y : Fin n → E) - y') ∈ M
        rw [← hco y, ← hco y', ← Finset.sum_sub_distrib]
        simp only [← sub_smul]
        refine comb_mem L b _ fun i => ?_
        rw [← L.cj_cj (co y i - co y' i)]
        refine cj_mem L ((L.additive_character_dual_ring _).1 fun t ht => ?_)
        have h1 := DFunLike.congr_fun h (Pi.single i ⟨t, ht⟩)
        have h2 : ∀ z, β z (Pi.single i ⟨t, ht⟩) = L.cj (co z i) * t := fun z => by
          change ∑ j, _ = _
          rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
          simp
        simp only [AddChar.compAddMonoidHom_apply, h2] at h1
        have h3 := L.psi0.map_add_eq_mul (L.cj (co y' i) * t) (-(L.cj (co y' i) * t))
        rw [map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← h3]
        simp)
    have hfin : Finite (N ⧸ M.comap N.subtype) := Nat.finite_of_card_ne_zero (fun h => hne (by
      rw [← hmul]; exact mul_eq_zero_of_left h _))
    obtain ⟨i, hi⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L ϖ hϖ
      (N ⧸ M.comap N.subtype)).1
    have hi' : (M.toAddSubgroup.addSubgroupOf N.toAddSubgroup).index = resQ ϖ ^ i := hi
    refine ⟨i, ?_, hi'⟩
    rw [hi'] at hmul hidx
    have h9 : resQ ϖ ^ (2 * i) ≤ resQ ϖ ^ (2 * a) := by
      rw [← hmul, two_mul, pow_add]; exact Nat.mul_le_mul_left _ hidx
    have := (Nat.pow_le_pow_iff_right (by omega)).1 h9
    omega
end GlobalTheory.HL.Defect
