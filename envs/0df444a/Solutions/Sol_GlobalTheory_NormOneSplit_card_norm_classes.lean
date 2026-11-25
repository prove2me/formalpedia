-- Prove2me | solution 1 for GlobalTheory.NormOneSplit.card_norm_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:39.3723+00:00
-- url     : https://prove2.me/submissions/54225d3d-a979-40b1-9b43-332ed8a9186c

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq
import Theorems.Thm_GlobalTheory_NormOneSplit_ker_isMaximal
import Theorems.Thm_GlobalTheory_NormOneSplit_mem_span_iff
import Theorems.Thm_GlobalTheory_NormOneSplit_finite_hom
import Theorems.Thm_GlobalTheory_NormOneSplit_exists_forall_hom_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
open NumberField Module Matrix in
open scoped ENNReal in
private theorem card_solutions_mul_involution_eq_pow {H K : Type} [Finite H] [Field K] [Fintype K]
    (ι : H → H) (hι : ∀ h, ι (ι h) = h) (hfix : ∀ h, ι h ≠ h) (c : H → K)
    (hc0 : ∀ h, c h ≠ 0) (hcι : ∀ h, c (ι h) = c h) :
    ∃ m, 2 * m = Nat.card H ∧
      Nat.card {f : H → K // ∀ h, f h * f (ι h) = c h} = (Fintype.card K - 1) ^ m := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : LinearOrder H := LinearOrder.lift' (Fintype.equivFin H) (Fintype.equivFin H).injective
  have hlt : ∀ h, ¬ h < ι h → ι h < ι (ι h) := fun h hh => by
    rw [hι]; exact lt_of_le_of_ne (not_lt.1 hh) (hfix h)
  have hnlt : ∀ h, h < ι h → ¬ ι h < ι (ι h) := fun h hh => by
    rw [hι]; exact not_lt.2 hh.le
  refine ⟨Nat.card {h : H // h < ι h}, ?_, ?_⟩
  · let e : H ≃ {h : H // h < ι h} ⊕ {h : H // h < ι h} :=
      { toFun := fun h => if hh : h < ι h then Sum.inl ⟨h, hh⟩ else Sum.inr ⟨ι h, hlt h hh⟩
        invFun := fun s => Sum.elim (fun a => a.1) (fun a => ι a.1) s
        left_inv := fun h => by
          by_cases hh : h < ι h
          · simp [hh]
          · simp [hh, hι]
        right_inv := fun s => by
          rcases s with ⟨a, ha⟩ | ⟨a, ha⟩
          · simp [ha]
          · have : ¬ ι a < ι (ι a) := hnlt a ha
            dsimp only [Sum.elim_inr]
            rw [dif_neg this]
            exact congrArg Sum.inr (Subtype.ext (hι a)) }
    rw [Nat.card_congr e, Nat.card_sum]; ring
  · let e : {f : H → K // ∀ h, f h * f (ι h) = c h} ≃ ({h : H // h < ι h} → {x : K // x ≠ 0}) :=
      { toFun := fun f a => ⟨f.1 a.1, fun h0 => hc0 a.1 (by rw [← f.2 a.1, h0, zero_mul])⟩
        invFun := fun g => ⟨fun h => if hh : h < ι h then (g ⟨h, hh⟩).1
            else c h / (g ⟨ι h, hlt h hh⟩).1, fun h => by
          by_cases hh : h < ι h
          · dsimp only
            rw [dif_pos hh, dif_neg (hnlt h hh)]
            have hg := (g ⟨h, hh⟩).2
            have hs : (⟨ι (ι h), hlt (ι h) (hnlt h hh)⟩ : {h : H // h < ι h}) = ⟨h, hh⟩ :=
              Subtype.ext (hι h)
            rw [hs, hcι]
            field_simp
          · dsimp only
            rw [dif_neg hh, dif_pos (hlt h hh)]
            have hg := (g ⟨ι h, hlt h hh⟩).2
            field_simp⟩
        left_inv := fun f => by
          apply Subtype.ext
          funext h
          by_cases hh : h < ι h
          · simp [hh]
          · simp only [dif_neg hh]
            have hf := f.2 h
            have hne : f.1 (ι h) ≠ 0 := fun h0 => hc0 h (by rw [← hf, h0, mul_zero])
            rw [div_eq_iff hne, hf]
        right_inv := fun g => by
          funext a
          apply Subtype.ext
          simp [a.2] }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr unitsEquivNeZero.symm, Nat.card_eq_fintype_card,
      Fintype.card_units]
open NumberField Module Matrix in
open scoped ENNReal in
private theorem comp_mapRingHom_star_ne_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hcm : _root_.Formalism.BasicNotions.CMData F E) {T : ℕ} (hT : T.Prime)
    (hs : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((T : 𝓞 E) ∈ P) →
      Ideal.absNorm P = T ∧ (T : 𝓞 E) ∉ P ^ 2) (φ : 𝓞 E →+* ZMod T) :
    φ.comp (RingOfIntegers.mapRingHom (starRingEnd E)) ≠ φ := by
  intro hφ
  haveI : Fact T.Prime := ⟨hT⟩
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut)
    (fun x => (hcm.fixed _).2 ⟨x, rfl⟩)
  have hσ : ∀ a : E, σ a = star a := fun a => rfl
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      have ha : star a = a := by rw [← hσ, h1]; rfl
      obtain ⟨y, hy⟩ := (hcm.fixed a).1 ha
      exact Algebra.mem_bot.2 ⟨y, hy⟩
    have h1' := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [hcm.deg2] at h1'
    norm_num at h1'
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hcm.deg2
  have h2 : 1 < Nat.card (E ≃ₐ[F] E) := by
    haveI : Nontrivial (E ≃ₐ[F] E) := ⟨⟨σ, 1, hσ1⟩⟩
    exact Finite.one_lt_card
  have hle : Nat.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hcm.deg2, Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [hcm.deg2]; omega)
  set P := RingHom.ker φ with hP
  haveI hPm : P.IsMaximal := _root_.GlobalTheory.NormOneSplit.ker_isMaximal φ
  have hmem : σ ∈ P.inertia (E ≃ₐ[F] E) := by
    intro x
    change σ • x - x ∈ RingHom.ker φ
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have hx : σ • x = RingOfIntegers.mapRingHom (starRingEnd E) x := Subtype.ext rfl
    rw [hx]
    exact RingHom.congr_fun hφ x
  have hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[F] E)]
  have h2le : 2 ≤ Nat.card (P.inertia (E ≃ₐ[F] E)) := by
    haveI : Nontrivial (P.inertia (E ≃ₐ[F] E)) :=
      ⟨⟨⟨σ, hmem⟩, 1, fun h => hσ1 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hTP : (T : 𝓞 E) ∈ P := by simp [hP, RingHom.mem_ker]
  have hTunder : (T : 𝓞 F) ∈ P.under (𝓞 F) := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using hTP
  have hTmap : (T : 𝓞 E) ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)) := by
    simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hTunder
  have hne : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)) ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at hTmap
    exact (Nat.cast_ne_zero.mpr hT.ne_zero) hTmap
  have hle2 := Ideal.le_pow_ramificationIdx (p := P.under (𝓞 F)) (P := P)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx' _ _ hne, ← hcard] at hle2
  exact (hs P hPm hTP).2 (Ideal.pow_le_pow_right h2le (hle2 hTmap))
end GlobalTheory.NormOneSplit
end

set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
namespace _root_.GlobalTheory.NormOneSplit
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 E), P.IsMaximal → ((T : 𝓞 E) ∈ P) → Ideal.absNorm P = T ∧ (T : 𝓞 E) ∉ P ^ 2) → ∀ c : 𝓞 E, star (c : E) = (c : E) → IsCoprime c (T : 𝓞 E) → Nat.card {a : 𝓞 E ⧸ Ideal.span {(T : 𝓞 E)} // ∃ x y : 𝓞 E, Ideal.Quotient.mk _ x = a ∧ (y : E) = star (x : E) ∧ x * y - c ∈ Ideal.span {(T : 𝓞 E)}} = (T - 1) ^ finrank ℚ F := by
  intro F E _ _ _ _ _ _ hcm T hT hs c hc hcop
  haveI : Fact T.Prime := ⟨hT⟩
  haveI := _root_.GlobalTheory.NormOneSplit.finite_hom (E := E) hT
  set τ := RingOfIntegers.mapRingHom (starRingEnd E) with hτdef
  have hτc : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hττ : ∀ x, τ (τ x) = x := fun x =>
    Subtype.ext ((hτc (τ x)).trans ((congrArg star (hτc x)).trans (star_star _)))
  let ev : (𝓞 E ⧸ Ideal.span {(T : 𝓞 E)}) →+* ((𝓞 E →+* ZMod T) → ZMod T) :=
    Pi.ringHom (fun φ => Ideal.Quotient.lift (Ideal.span {(T : 𝓞 E)}) φ (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha; simp))
  have hev : ∀ x φ, ev (Ideal.Quotient.mk _ x) φ = φ x := fun x φ => rfl
  have hbij : Function.Bijective ev := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.eq_zero_iff_mem, _root_.GlobalTheory.NormOneSplit.mem_span_iff hT hs]
      intro φ
      rw [← hev]
      exact congrFun ha φ
    · intro f
      obtain ⟨x, hx⟩ := _root_.GlobalTheory.NormOneSplit.exists_forall_hom_eq f
      exact ⟨Ideal.Quotient.mk _ x, funext fun φ => by rw [hev, hx]⟩
  have hA : Nat.card {a : 𝓞 E ⧸ Ideal.span {(T : 𝓞 E)} // ∃ x y : 𝓞 E,
      Ideal.Quotient.mk _ x = a ∧ (y : E) = star (x : E) ∧ x * y - c ∈ Ideal.span {(T : 𝓞 E)}} =
      Nat.card {f : (𝓞 E →+* ZMod T) → ZMod T // ∀ φ, f φ * f (φ.comp τ) = φ c} := by
    refine Nat.card_congr ((Equiv.ofBijective ev hbij).subtypeEquiv fun a => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    change _ ↔ ∀ φ : 𝓞 E →+* ZMod T, ev (Ideal.Quotient.mk _ x) φ *
      ev (Ideal.Quotient.mk _ x) (φ.comp τ) = φ c
    simp only [hev]
    constructor
    · rintro ⟨x', y, hx', hy, hxy⟩ φ
      have hyτ : y = τ x' := Subtype.ext (hy.trans (hτc x').symm)
      rw [Ideal.Quotient.eq, _root_.GlobalTheory.NormOneSplit.mem_span_iff hT hs] at hx'
      have h1 := hx' φ
      have h2 := hx' (φ.comp τ)
      have h3 := (_root_.GlobalTheory.NormOneSplit.mem_span_iff hT hs _).1 hxy φ
      rw [map_sub, sub_eq_zero] at h1 h2 h3
      rw [← h1, ← h2, ← h3, hyτ, map_mul, RingHom.comp_apply]
    · intro h
      refine ⟨x, τ x, rfl, hτc x, ?_⟩
      rw [_root_.GlobalTheory.NormOneSplit.mem_span_iff hT hs]
      intro φ
      rw [map_sub, map_mul, sub_eq_zero]
      exact h φ
  have hT0 : ∀ φ : 𝓞 E →+* ZMod T, φ (T : 𝓞 E) = 0 := fun φ => by simp
  have hc0 : ∀ φ : 𝓞 E →+* ZMod T, φ c ≠ 0 := by
    intro φ h0
    obtain ⟨a, b, hab⟩ := hcop
    have := congrArg φ hab
    rw [map_add, map_mul, map_mul, h0, hT0, map_one] at this
    simp at this
  have hτcc : τ c = c := Subtype.ext ((hτc c).trans hc)
  obtain ⟨m, hm, hcount⟩ := card_solutions_mul_involution_eq_pow (fun φ : 𝓞 E →+* ZMod T => φ.comp τ)
    (fun φ => RingHom.ext fun x => by simp [hττ]) (fun φ => comp_mapRingHom_star_ne_of_split hcm hT hs φ)
    (fun φ => φ c) hc0 (fun φ => by simp [hτcc])
  rw [hA, hcount, ZMod.card]
  congr 1

  have hcardQ : Nat.card (𝓞 E ⧸ Ideal.span {(T : 𝓞 E)}) = T ^ finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
    have hTmap : (T : 𝓞 E) = algebraMap ℤ (𝓞 E) (T : ℤ) := by simp
    rw [hTmap, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  have hcardH : Nat.card (𝓞 E →+* ZMod T) = finrank ℚ E := by
    have h := Nat.card_congr (Equiv.ofBijective ev hbij)
    rw [hcardQ, Nat.card_fun, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hT.two_le h).symm
  have hdeg : finrank ℚ E = finrank ℚ F * 2 := by
    rw [← Module.finrank_mul_finrank ℚ F E, hcm.deg2]
  omega
end _root_.GlobalTheory.NormOneSplit
end GlobalTheory.NormOneSplit
