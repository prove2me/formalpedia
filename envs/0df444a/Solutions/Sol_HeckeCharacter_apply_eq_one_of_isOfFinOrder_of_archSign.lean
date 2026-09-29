-- Prove2me | solution 1 for HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bfc27a7d-eebb-5022-b15b-be56e29a634c

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeOf archSign"
namespace TotallyPositiveArchRoot
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

private noncomputable def rootAt {n : ℕ} (hn : 0 < n) (w : InfinitePlace K) (x : w.Completion) : w.Completion :=
  if hw : w.IsReal then
    (ringEquivRealOfIsReal hw).symm ((ringEquivRealOfIsReal hw x) ^ ((n : ℝ)⁻¹))
  else
    (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm
      (Classical.choose
        (IsAlgClosed.exists_pow_nat_eq (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw) x) hn))

omit [NumberField K] in
open scoped Classical in
private theorem rootAt_pow {n : ℕ} (hn : 0 < n) (w : InfinitePlace K) (x : w.Completion)
    (hx : ∀ hw : w.IsReal, 0 ≤ ringEquivRealOfIsReal hw x) : rootAt K hn w x ^ n = x := by
  unfold rootAt
  split_ifs with hw
  · rw [← map_pow, Real.rpow_inv_natCast_pow (hx hw) hn.ne', RingEquiv.symm_apply_apply]
  · rw [← map_pow, Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw) x) hn), RingEquiv.symm_apply_apply]

omit [NumberField K] in

private theorem placeOf_embedding_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    placeOf K (embedding_of_isReal hw) = w := by
  show InfinitePlace.mk (Complex.ofRealHom.comp (embedding_of_isReal hw)) = w
  have e : Complex.ofRealHom.comp (embedding_of_isReal hw) = w.embedding :=
    RingHom.ext fun x => embedding_of_isReal_apply hw x
  rw [e, mk_embedding]

private noncomputable def archUnitsToIdeles : (InfiniteAdeleRing K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

end HeckeCharacter.TotallyPositiveArchRoot

open HeckeCharacter.TotallyPositiveArchRoot in
theorem solution
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommMonoid M]
    (η : (AdeleRing (𝓞 K) K)ˣ →* M) (hη : IsOfFinOrder η)
    (u : (AdeleRing (𝓞 K) K)ˣ) (hfin : (u : AdeleRing (𝓞 K) K).2 = 1)
    (hpos : ∀ τ : K →+* ℝ, HeckeCharacter.archSign K τ u) :
    η u = 1 := by
  have hn : 0 < orderOf η := hη.orderOf_pos

  have hposw : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < ringEquivRealOfIsReal hw ((u : AdeleRing (𝓞 K) K).1 w) := by
    intro w hw
    have key : ∀ (τ : K →+* ℝ) (h : (HeckeCharacter.placeOf K τ).IsReal),
        0 < ringEquivRealOfIsReal h ((u : AdeleRing (𝓞 K) K).1 (HeckeCharacter.placeOf K τ)) :=
      fun τ _ => hpos τ
    have := key (embedding_of_isReal hw)
    rw [placeOf_embedding_of_isReal K hw] at this
    exact this hw

  have ha : ∀ w : InfinitePlace K, (u : AdeleRing (𝓞 K) K).1 w ≠ 0 := by
    intro w
    have h1 : ((u * u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
      rw [mul_inv_cancel]; rfl
    rw [Units.val_mul] at h1
    exact left_ne_zero_of_mul_eq_one h1

  let r : (w : InfinitePlace K) → w.Completion :=
    fun w => rootAt K hn w ((u : AdeleRing (𝓞 K) K).1 w)
  have hr_pow : ∀ w, r w ^ orderOf η = (u : AdeleRing (𝓞 K) K).1 w :=
    fun w => rootAt_pow K hn w _ fun hw => (hposw w hw).le
  have hr_ne : ∀ w, r w ≠ 0 := by
    intro w h
    apply ha w
    rw [← hr_pow w, h, zero_pow hn.ne']

  let t : (InfiniteAdeleRing K)ˣ :=
    ⟨(fun w => r w : InfiniteAdeleRing K), (fun w => (r w)⁻¹ : InfiniteAdeleRing K),
      funext fun w => mul_inv_cancel₀ (hr_ne w), funext fun w => inv_mul_cancel₀ (hr_ne w)⟩
  obtain ⟨v, hv⟩ : ∃ v : (AdeleRing (𝓞 K) K)ˣ, v ^ orderOf η = u := by
    refine ⟨archUnitsToIdeles K t, ?_⟩
    rw [← map_pow (archUnitsToIdeles K) t (orderOf η)]
    refine Units.ext ?_
    show ((((t ^ orderOf η : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K)) :
      AdeleRing (𝓞 K) K) = (u : AdeleRing (𝓞 K) K)
    refine Prod.ext (funext fun w => ?_) hfin.symm
    show r w ^ orderOf η = (u : AdeleRing (𝓞 K) K).1 w
    exact hr_pow w

  calc η u = η (v ^ orderOf η) := by rw [hv]
    _ = (η ^ orderOf η) v := by rw [map_pow, MonoidHom.pow_apply]
    _ = 1 := by rw [pow_orderOf_eq_one, MonoidHom.one_apply]

end S_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign
end P2MW
export P2MW.S_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign (solution)
