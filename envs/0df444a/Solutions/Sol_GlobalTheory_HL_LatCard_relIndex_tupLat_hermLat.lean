-- Prove2me | solution 1 for GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:32.839679+00:00
-- url     : https://prove2.me/submissions/65d6d6bd-d294-482c-899e-12d7789005ec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
import Theorems.Thm_GlobalTheory_HL_LatCard_relIndex_map_of_param
import Theorems.Thm_GlobalTheory_HL_LatCard_card_pairs
import Theorems.Thm_GlobalTheory_HL_LatCard_hermOf_apply
import Theorems.Thm_GlobalTheory_HL_LatCard_hf_sum_smul
import Theorems.Thm_GlobalTheory_HL_LatCard_tupOf_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_orthonormal
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.LatCard
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
private theorem index_range_smul_pi {R M ι : Type*} [Monoid R] [AddCommGroup M]
    [DistribMulAction R M] [Fintype ι] (r : R) :
    (DistribMulAction.toAddMonoidHom (ι → M) r).range.index =
      (DistribMulAction.toAddMonoidHom M r).range.index ^ Fintype.card ι := by
  have h : (DistribMulAction.toAddMonoidHom (ι → M) r).range =
      AddSubgroup.pi Set.univ (fun _ => (DistribMulAction.toAddMonoidHom M r).range) := by
    ext x
    simp only [AddMonoidHom.mem_range, DistribMulAction.toAddMonoidHom_apply, AddSubgroup.mem_pi,
      Set.mem_univ, true_imp_iff]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, rfl⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, funext hy⟩
  rw [h, AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ]
private theorem index_range_smul_pow {R : Type*} [CommRing R] [IsDomain R] {r : R} (hr : r ≠ 0)
    (j : ℕ) : (DistribMulAction.toAddMonoidHom R (r ^ j)).range.index =
      (DistribMulAction.toAddMonoidHom R r).range.index ^ j := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero]
    convert AddSubgroup.index_top
    ext x
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact ⟨x, one_smul R x⟩
  | succ j ih =>
    have hinj : Function.Injective (DistribMulAction.toAddMonoidHom R r) := fun x y h =>
      mul_left_cancel₀ hr (by simpa using h)
    have hmap : (DistribMulAction.toAddMonoidHom R (r ^ (j + 1))).range =
        (DistribMulAction.toAddMonoidHom R (r ^ j)).range.map
          (DistribMulAction.toAddMonoidHom R r) := by
      ext x
      simp only [AddMonoidHom.mem_range, AddSubgroup.mem_map, DistribMulAction.toAddMonoidHom_apply,
        smul_eq_mul]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨r ^ j * y, ⟨y, rfl⟩, by ring⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨y, by ring⟩
    rw [hmap, AddSubgroup.index_map_of_injective _ hinj, ih, pow_succ]
private theorem index_range_smul_eq_card_quotient {R : Type*} [CommRing R] (r : R) :
    (DistribMulAction.toAddMonoidHom R r).range.index = Nat.card (R ⧸ Ideal.span {r}) := by
  have h : (DistribMulAction.toAddMonoidHom R r).range = (Ideal.span {r}).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_range, DistribMulAction.toAddMonoidHom_apply, smul_eq_mul,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, mul_comm _ _⟩
  rw [h, AddSubgroup.index_eq_card]
  rfl
end GlobalTheory.HL.LatCard
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatCard
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.LatCard
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m j : ℕ, ((tupLat L Λs m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))).relIndex (tupLat L Λs m) = resQ ϖ ^ (2 * n * m * j) ∧ ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))).relIndex (hermLat L m) = resQ ϖ ^ (m ^ 2 * j) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m j
  obtain ⟨b, hbo, hΛb⟩ := GlobalTheory.HL.SelfDual.exists_orthonormal L hH hΛ
  have hmemO : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ L.O := fun c =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2
  have cj_alg : ∀ c : F, L.cj (algebraMap F E c) = algebraMap F E c := fun c => L.cj.commutes c
  have hsmem : algebraMap F E ((ϖ : F) ^ j) ∈ L.O := by exact_mod_cast hmemO (ϖ ^ j)
  obtain ⟨sO, hsO⟩ : ∃ sO : L.O, (sO : E) = algebraMap F E ((ϖ : F) ^ j) := ⟨⟨_, hsmem⟩, rfl⟩
  have hord := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.2.2.1 j
  have hset : ({y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} : Set L.O) = {sO} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff, hsO]
  rw [hset] at hord
  have hqO : (DistribMulAction.toAddMonoidHom L.O sO).range.index = resQ ϖ ^ (2 * j) := by
    rw [index_range_smul_eq_card_quotient, hord]
  have hqF : (DistribMulAction.toAddMonoidHom 𝒪[F] (ϖ ^ j)).range.index = resQ ϖ ^ j := by
    rw [index_range_smul_pow hϖ.ne_zero, index_range_smul_eq_card_quotient]
    rfl
  have hpair : ∀ (x : Fin n → L.O) (k : Fin n), hf L Hm (∑ i, (x i : E) • b i) (b k) = x k := by
    intro x k
    rw [hf_sum_smul]
    simp [hbo]
  have hinj1 : Function.Injective (tupOf L b m) := by
    intro x x' h
    funext a k
    apply Subtype.ext
    have := congrArg (fun w => hf L Hm (w a) (b k)) h
    simpa only [tupOf_apply, hpair] using this
  have hA1 : ∀ w, w ∈ tupLat L Λs m ↔ ∃ g, tupOf L b m g = w := by
    intro w
    simp only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_toAddSubgroup,
      hΛb, Submodule.mem_span_range_iff_exists_fun, Subring.smul_def]
    constructor
    · intro hw
      choose g hg using hw
      exact ⟨g, funext fun a => by rw [tupOf_apply]; exact hg a⟩
    · rintro ⟨g, rfl⟩ a
      exact ⟨g a, (tupOf_apply L b m g a).symm⟩
  have ht1 : ∀ g, tupOf L b m (DistribMulAction.toAddMonoidHom _ sO g) =
      DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)) (tupOf L b m g) := by
    intro g
    funext a
    simp only [DistribMulAction.toAddMonoidHom_apply, tupOf_apply, Pi.smul_apply, smul_eq_mul,
      MulMemClass.coe_mul, hsO, mul_smul, Finset.smul_sum]
  have P1 := relIndex_map_of_param (tupOf L b m) hinj1 (tupLat L Λs m) hA1
    (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))
    (DistribMulAction.toAddMonoidHom _ sO) ht1 _ (fun g => AddMonoidHom.mem_range)
  rw [index_range_smul_pi, index_range_smul_pi, hqO, Fintype.card_fin, Fintype.card_fin] at P1
  have herm_iff : ∀ X : Matrix (Fin m) (Fin m) E, IsHerm L X ↔ ∀ a b, L.cj (X b a) = X a b :=
    fun X => ⟨fun h a b => congrFun (congrFun h a) b, fun h => Matrix.ext h⟩
  have hermMem : ∀ X, X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
    intro X
    constructor
    · intro hX
      unfold hermLat at hX
      induction hX using AddSubgroup.closure_induction with
      | mem x hx => exact hx
      | zero =>
        refine ⟨(herm_iff _).2 fun a b => ?_, fun a b => ?_⟩
        · simp
        · simp only [Matrix.zero_apply]
          exact L.O.zero_mem
      | add x y _ _ hx hy =>
        refine ⟨(herm_iff _).2 fun a b => ?_, fun a b => ?_⟩
        · simp [(herm_iff _).1 hx.1 a b, (herm_iff _).1 hy.1 a b]
        · simpa only [Matrix.add_apply] using add_mem (hx.2 a b) (hy.2 a b)
      | neg x _ hx =>
        refine ⟨(herm_iff _).2 fun a b => ?_, fun a b => ?_⟩
        · simp [(herm_iff _).1 hx.1 a b]
        · simpa only [Matrix.neg_apply] using neg_mem (hx.2 a b)
    · intro hX
      exact AddSubgroup.subset_closure hX
  have hinj2 : Function.Injective (hermOf L m) := by
    intro x y h
    have hd : ∀ a b, hermOf L m x a b = hermOf L m y a b := fun a b => by rw [h]
    refine Prod.ext (funext fun a => ?_) (funext fun p => ?_)
    · have := hd a a
      rw [hermOf_apply, hermOf_apply, dif_neg (lt_irrefl a), dif_neg (lt_irrefl a),
        dif_neg (lt_irrefl a), dif_neg (lt_irrefl a)] at this
      exact Subtype.ext (GlobalTheory.UnramOrder.algebraMap_inj L this)
    · have := hd p.1.1 p.1.2
      rw [hermOf_apply, hermOf_apply, dif_pos p.2, dif_pos p.2] at this
      exact Subtype.ext this
  have hA2 : ∀ X, X ∈ hermLat L m ↔ ∃ g, hermOf L m g = X := by
    intro X
    rw [hermMem]
    constructor
    · rintro ⟨hHX, hIX⟩
      have diag : ∀ a, ∃ c : 𝒪[F], X a a = algebraMap F E c := fun a =>
        GlobalTheory.UnramOrder.exists_int_of_fixed L (hIX a a) ((herm_iff X).1 hHX a a)
      choose d hd using diag
      refine ⟨(d, fun p => ⟨X p.1.1 p.1.2, hIX _ _⟩), ?_⟩
      ext a b
      rw [hermOf_apply]
      split_ifs with h h'
      · rfl
      · exact (herm_iff X).1 hHX a b
      · have hab : a = b := le_antisymm (not_lt.1 h') (not_lt.1 h)
        subst hab
        exact (hd a).symm
    · rintro ⟨g, rfl⟩
      refine ⟨(herm_iff _).2 fun a b => ?_, fun a b => ?_⟩
      · rcases lt_trichotomy a b with h | rfl | h
        · simp [hermOf_apply, h, not_lt.2 h.le, L.cj_cj]
        · simp [hermOf_apply, cj_alg]
        · simp [hermOf_apply, h, not_lt.2 h.le]
      · rw [hermOf_apply]
        split_ifs
        · exact Subtype.prop _
        · exact GlobalTheory.UnramOrder.cj_mem L (Subtype.prop _)
        · exact hmemO _
  have ht2 : ∀ g, hermOf L m (((DistribMulAction.toAddMonoidHom (Fin m → 𝒪[F]) (ϖ ^ j)).prodMap
      (DistribMulAction.toAddMonoidHom ({p : Fin m × Fin m // p.1 < p.2} → L.O) sO)) g) =
      DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)) (hermOf L m g) := by
    intro g
    ext a b
    simp only [DistribMulAction.toAddMonoidHom_apply, Matrix.smul_apply, hermOf_apply,
      AddMonoidHom.coe_prodMap, Prod.map_fst, Prod.map_snd, Prod.map_apply]
    split_ifs <;> simp [smul_eq_mul, MulMemClass.coe_mul, hsO, cj_alg, map_mul]
  have hR2 : ((DistribMulAction.toAddMonoidHom (Fin m → 𝒪[F]) (ϖ ^ j)).prodMap
      (DistribMulAction.toAddMonoidHom ({p : Fin m × Fin m // p.1 < p.2} → L.O) sO)).range =
      (DistribMulAction.toAddMonoidHom (Fin m → 𝒪[F]) (ϖ ^ j)).range.prod
        (DistribMulAction.toAddMonoidHom ({p : Fin m × Fin m // p.1 < p.2} → L.O) sO).range := by
    ext ⟨x, y⟩
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, AddMonoidHom.coe_prodMap, Prod.exists,
      Prod.map_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨u, v, h1, h2⟩
      exact ⟨⟨u, h1⟩, ⟨v, h2⟩⟩
    · rintro ⟨⟨u, h1⟩, ⟨v, h2⟩⟩
      exact ⟨u, v, h1, h2⟩
  have P2 := relIndex_map_of_param (hermOf L m) hinj2 (hermLat L m) hA2
    (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j))) _ ht2 _
    (fun g => AddMonoidHom.mem_range)
  rw [hR2, AddSubgroup.index_prod, index_range_smul_pi, index_range_smul_pi, hqF, hqO,
    Fintype.card_fin] at P2
  refine ⟨?_, ?_⟩
  · rw [P1]
    ring
  · rw [P2, ← card_pairs m]
    ring
end GlobalTheory.HL.LatCard
