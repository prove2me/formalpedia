-- Prove2me | solution 1 for GlobalTheory.UnramOrder.order_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:02.699634+00:00
-- url     : https://prove2.me/submissions/f2c843b8-4270-4819-8458-f7c3988280ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_card_quot_eq_sq
import Theorems.Thm_GlobalTheory_UnramOrder_isPrincipalIdealRing_of_henselian
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_trace
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.UnramOrder
namespace GlobalTheory.UnramOrder
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ c : 𝒪[F], ∃ x ∈ L.O, x + L.cj x = algebraMap F E c) ∧ (∀ x ∈ L.O, L.cj x ∈ L.O ∧ (∃ c : 𝒪[F], x + L.cj x = algebraMap F E c) ∧ ∃ c : 𝒪[F], x * L.cj x = algebraMap F E c) ∧ (∀ x : E, (∀ b ∈ L.O, ∃ c : 𝒪[F], x * L.cj b + L.cj (x * L.cj b) = algebraMap F E c) → x ∈ L.O) ∧ IsPrincipalIdealRing L.O ∧ (∀ c : F, algebraMap F E c ∈ L.O ↔ c ∈ 𝒪[F]) ∧ (∀ j : ℕ, Nat.card (L.O ⧸ (Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)})) = resQ ϖ ^ (2 * j)) ∧ 2 ≤ resQ ϖ ∧ (∀ u : (𝒪[F])ˣ, ∃ x ∈ L.O, x * L.cj x = algebraMap F E ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  obtain ⟨ω, hω, e, he, hωe⟩ := exists_sub_cj_mul_eq_one L
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hal : ∀ a : 𝒪[F], ((algebraMap 𝒪[F] L.O a : L.O) : E) = algebraMap F E a := fun _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  have hbase : ∀ r, c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r := fun r =>
    Subtype.ext (by rw [hcv, hal, AlgEquiv.commutes])
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  have hu : IsUnit ((⟨ω, hω⟩ : L.O) - c ⟨ω, hω⟩) :=
    IsUnit.of_mul_eq_one ⟨e, he⟩ (Subtype.ext hωe)
  have hD : ∀ r : 𝒪[F], IsUnit (algebraMap 𝒪[F] L.O r) → IsUnit r := fun r hr => by
    obtain ⟨y, hy⟩ := hr.exists_right_inv
    have hy' := congrArg c hy
    rw [map_mul, hbase, map_one] at hy'
    obtain ⟨s, rfl⟩ := hfix y (by
      linear_combination y * hy' - c y * hy)
    exact IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hy, map_one]))
  have hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F]) := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hm := hϖ.maximalIdeal_eq
  refine ⟨fun a => ⟨algebraMap F E a * (ω * e), L.O.mul_mem (hint a) (L.O.mul_mem hω he), ?_⟩,
    fun x hx => ⟨cj_mem L hx, exists_trace L hx, exists_norm L hx⟩, fun x hx => ?_,
    isPrincipalIdealRing_of_henselian c hc hbase hfix hu hD, algebraMap_mem_iff L,
    fun j => ?_, ?_, fun u => ?_⟩
  · simp only [map_mul, AlgEquiv.commutes, hce]
    linear_combination algebraMap F E a * hωe
  · obtain ⟨s, hs⟩ := hx 1 L.O.one_mem
    obtain ⟨r, hr⟩ := hx ω hω
    simp only [map_mul, map_one, mul_one, L.cj_cj] at hs hr
    have : x = (algebraMap F E s * ω - algebraMap F E r) * e := by
      rw [← hs, ← hr]
      linear_combination (-x) * hωe
    rw [this]
    exact L.O.mul_mem (L.O.sub_mem (L.O.mul_mem (hint s) hω) (hint r)) he
  · have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
        = {algebraMap 𝒪[F] L.O (ϖ ^ j)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff, hal, Subring.coe_pow]
    have hp : (Ideal.span {ϖ}).IsPrime := hm ▸ inferInstance
    have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
      (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := j)
    rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
    rw [hset, card_quot_eq_sq c hc hbase hinj hfix hu, hq, resQ, ← pow_mul, mul_comm]
  · rw [resQ, ← hm]
    have : Finite (IsLocalRing.ResidueField 𝒪[F]) := inferInstance
    exact Finite.one_lt_card (α := IsLocalRing.ResidueField 𝒪[F])
  · obtain ⟨x, hx⟩ := GlobalTheory.UnramifiedHermitian.exists_norm_eq_of_henselian (R₀ := 𝒪[F]) c hc hbase
      hfix ⟨_, hu⟩ (hbase u) (u.isUnit.map _)
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
end GlobalTheory.UnramOrder
