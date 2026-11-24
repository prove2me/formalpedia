-- Prove2me | solution 1 for GlobalTheory.UnramOrder.card_quot_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:27.229279+00:00
-- url     : https://prove2.me/submissions/77517458-35d8-4346-81f9-ba2435448ea5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_add_mul
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
open IsLocalRing Polynomial
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
namespace GlobalTheory.UnramOrder
theorem _root_.solution (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hinj : Function.Injective (algebraMap R₀ R))
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω)) (p : R₀) :
    Nat.card (R ⧸ Ideal.span {algebraMap R₀ R p}) = Nat.card (R₀ ⧸ Ideal.span {p}) ^ 2 := by
  let φ : R₀ × R₀ →+ R :=
    { toFun := fun z => algebraMap R₀ R z.1 + algebraMap R₀ R z.2 * ω
      map_zero' := by simp
      map_add' := fun x y => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring }
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨a, b, h⟩ := exists_eq_add_mul c hc hbase hfix hω x
    exact ⟨(a, b), h.symm⟩
  have hind : ∀ a b : R₀, algebraMap R₀ R a + algebraMap R₀ R b * ω = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h' := congrArg c h
    rw [map_add, map_mul, hbase, hbase, map_zero] at h'
    have hb : algebraMap R₀ R b = 0 :=
      hω.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap R₀ R a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  have hcomap : (Ideal.span {algebraMap R₀ R p}).toAddSubgroup.comap φ
      = (Ideal.span {p}).toAddSubgroup.prod (Ideal.span {p}).toAddSubgroup := by
    ext ⟨a, b⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, v, rfl⟩ := exists_eq_add_mul c hc hbase hfix hω y
      obtain ⟨h1, h2⟩ := hind (a - p * u) (b - p * v) (by
        have hy' : algebraMap R₀ R a + algebraMap R₀ R b * ω = _ := hy
        simp only [map_sub, map_mul]
        linear_combination hy')
      exact ⟨⟨u, sub_eq_zero.1 h1⟩, ⟨v, sub_eq_zero.1 h2⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      refine ⟨algebraMap R₀ R u + algebraMap R₀ R v * ω, ?_⟩
      show algebraMap R₀ R _ + algebraMap R₀ R _ * ω = _
      simp only [map_mul]; ring
  have h := AddSubgroup.index_comap_of_surjective
    (Ideal.span {algebraMap R₀ R p}).toAddSubgroup hφ
  rw [hcomap, AddSubgroup.index_prod] at h
  rw [sq]
  exact h.symm
end GlobalTheory.UnramOrder
