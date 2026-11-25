-- Prove2me | solution 1 for GlobalTheory.PicDom.isOfFinOrder_of_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:13.824628+00:00
-- url     : https://prove2.me/submissions/7b5be597-9294-4268-b69f-c88ade741be8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
import Theorems.Thm_GlobalTheory_PicDom_exists_int_mem_span
import Theorems.Thm_GlobalTheory_T_isOfFinOrder_of_isOfFinOrder_pic_mapRingHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PicDom
variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]
namespace GlobalTheory.PicDom
theorem _root_.solution (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [NumberField K]
    (M : CommRing.Pic B) : IsOfFinOrder M := by
  let φ : B →+* 𝓞 K :=
    { toFun := fun b => ⟨algebraMap B K b, (Algebra.IsIntegral.isIntegral (R := ℤ) b).algebraMap⟩
      map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
      map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
      map_add' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_add]; rfl
      map_mul' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_mul]; rfl }
  have hφ : ∀ b, ((φ b : 𝓞 K) : K) = algebraMap B K b := fun b => rfl
  have hinj : Function.Injective φ := fun x y h => IsFractionRing.injective B K (by
    rw [← hφ, ← hφ, h])

  have hmul : ∀ ω : 𝓞 K, ∃ a : ℤ, a ≠ 0 ∧ (a : 𝓞 K) * ω ∈ φ.range := fun ω => by
    obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := B) (ω : K)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have hdK : algebraMap B K d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
    refine ⟨a, ha0, c * b, ?_⟩
    apply RingOfIntegers.ext
    rw [hφ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, ← hbd]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    rw [h2, mul_assoc]
    congr 1
    exact (mul_div_cancel₀ _ hdK).symm
  classical
  choose a ha0 ha using hmul
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 K)
  set N : ℤ := ∏ ω ∈ t, a ω
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun ω _ => ha0 ω
  have hNmem : ∀ x : 𝓞 K, (N : 𝓞 K) * x ∈ φ.range := fun x => by
    have hx : x ∈ Submodule.span ℤ (t : Set (𝓞 K)) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem ω hω =>
      show ((∏ ω ∈ t, a ω : ℤ) : 𝓞 K) * ω ∈ φ.range
      rw [← Finset.mul_prod_erase t a (Finset.mem_coe.1 hω), Int.cast_mul, mul_comm (a ω : 𝓞 K), mul_assoc]
      exact mul_mem (intCast_mem _ _) (ha ω)
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact zsmul_mem hx k
  have hn0 : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN0
  have hcond : ∀ x : 𝓞 K, ((N.natAbs : ℕ) : 𝓞 K) * x ∈ φ.range := fun x => by
    rcases Int.natAbs_eq N with h | h
    · have := hNmem x
      rwa [h, Int.cast_natCast] at this
    · have := neg_mem (hNmem x)
      rwa [h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
  haveI : Finite (CommRing.Pic (𝓞 K)) := Finite.of_equiv _ (ClassGroup.equivPic (𝓞 K)).toEquiv
  exact GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B (𝓞 K) φ N.natAbs hinj hn0 hcond M (isOfFinOrder_of_finite _)
end GlobalTheory.PicDom
