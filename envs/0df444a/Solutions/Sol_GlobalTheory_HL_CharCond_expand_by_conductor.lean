-- Prove2me | solution 1 for GlobalTheory.HL.CharCond.expand_by_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:39.537913+00:00
-- url     : https://prove2.me/submissions/66175ad9-a50a-4a0e-b87c-a191a2fda7a8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
namespace GlobalTheory.HL.CharCond
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem ker_mkQ_comp_mulLeft_pow_eq_span {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n k : ℕ) :
    ((Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))).ker =
      Ideal.span {ϖ ^ n} := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  rw [pow_add, mul_comm (ϖ ^ n), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_pow_succ_eq_resQ_mul {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ (n + 1)}) =
      _root_.GlobalTheory.HL.resQ ϖ * Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) := by
  rw [add_comm n 1]
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ n))
  have hS : Nat.card (LinearMap.range f) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    have hk := ker_mkQ_comp_mulLeft_pow_eq_span hϖ 1 n
    rw [pow_one] at hk
    rw [← hk]
    exact (Nat.card_congr (f.quotKerEquivRange).toEquiv).symm
  set g := (Submodule.mkQ (LinearMap.range f)).comp (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)}))
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : g.ker = Ideal.span {ϖ ^ n} := by
    ext y
    simp only [g, f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
      LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, hz⟩
      rw [Submodule.Quotient.eq, Ideal.mem_span_singleton] at hz
      have h2 : ϖ ^ n ∣ ϖ ^ (1 + n) := pow_dvd_pow _ (by omega)
      have h4 : ϖ ^ n ∣ ϖ ^ n * z := dvd_mul_right _ _
      simpa using (dvd_sub h4 (h2.trans hz))
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have e := (g.quotKerEquivOfSurjective hg).toEquiv
  rw [hker] at e
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f), hS, Nat.card_congr e]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_pow_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) = _root_.GlobalTheory.HL.resQ ϖ ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ n ih => rw [card_quotient_pow_succ_eq_resQ_mul hϖ, ih, pow_succ, mul_comm]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem resQ_pos_flag_measures {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [← h]
  exact Nat.card_pos (α := 𝓀[F])
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finite_quotient_span_pow' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) :=
  Nat.finite_of_card_ne_zero (by rw [card_quotient_pow_eq_resQ_pow hϖ]; exact pow_ne_zero _ (resQ_pos_flag_measures hϖ).ne')
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem addChar_mul_eq_of_quotient_eq {ϖ : 𝒪[F]} {ψ : AddChar F ℂ}
    (hψ : ∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) {a : ℕ} {c : F}
    (hc : c * (ϖ : F) ^ a ∈ 𝒪[F]) {y y' : 𝒪[F]}
    (h : Ideal.Quotient.mk (Ideal.span {ϖ ^ a}) y = Ideal.Quotient.mk _ y') :
    ψ (y * c) = ψ (y' * c) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  have hy : (y : F) = y' + w * (ϖ : F) ^ a := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) hw
    push_cast at this
    linear_combination -this
  have h1 : ψ (c * (ϖ : F) ^ a * w) = 1 := (hψ _).2 hc w
  rw [hy, show ((y' : F) + w * (ϖ : F) ^ a) * c = y' * c + c * (ϖ : F) ^ a * w by ring,
    AddChar.map_add_eq_mul, h1, mul_one]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mk_rep_eq (ϖ : 𝒪[F]) (a : ℕ)
    (r : 𝒪[F] ⧸ Ideal.span {ϖ ^ a}) :
    Ideal.Quotient.mk _ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r) = r :=
  (Ideal.Quotient.mk_surjective r).choose_spec
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem addChar_eq_one_of_mem_integer {ψ : AddChar F ℂ}
    (hψ : ∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) {c : F} (hc : c ∈ 𝒪[F]) :
    ψ c = 1 := by
  simpa using (hψ c).2 hc 1
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem sum_addChar_rep_mul_eq_ite {ϖ : 𝒪[F]} {ψ : AddChar F ℂ}
    (hψ : ∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) (a : ℕ)
    [Fintype (𝒪[F] ⧸ Ideal.span {ϖ ^ a})] {c : F} (hc : c * (ϖ : F) ^ a ∈ 𝒪[F]) :
    ∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) =
      if c ∈ 𝒪[F] then (Fintype.card (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) : ℂ) else 0 := by
  have hadd : ∀ r s, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a (r + s) * c) =
      ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) *
        ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a s * c) := by
    intro r s
    rw [← AddChar.map_add_eq_mul, ← add_mul]
    have := addChar_mul_eq_of_quotient_eq hψ hc (y := _root_.GlobalTheory.HL.CharCond.rep ϖ a (r + s))
      (y' := _root_.GlobalTheory.HL.CharCond.rep ϖ a r + _root_.GlobalTheory.HL.CharCond.rep ϖ a s)
      (by rw [map_add, mk_rep_eq,
        mk_rep_eq, mk_rep_eq])
    rw [this]
    push_cast
    rfl
  split_ifs with hcO
  · have : ∀ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) = 1 := fun r =>
      addChar_eq_one_of_mem_integer hψ (mul_mem (_root_.GlobalTheory.HL.CharCond.rep ϖ a r).2 hcO)
    simp [this]
  · have hne : ¬ ∀ y : 𝒪[F], ψ (c * y) = 1 := fun h => hcO ((hψ c).1 h)
    push_neg at hne
    obtain ⟨y, hy⟩ := hne
    set m : 𝒪[F] ⧸ Ideal.span {ϖ ^ a} := Ideal.Quotient.mk _ y
    have hm : ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a m * c) ≠ 1 := by
      rw [addChar_mul_eq_of_quotient_eq hψ hc (y' := y) (mk_rep_eq ϖ a m), mul_comm]
      exact hy
    have hshift : ∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c) =
        (∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c)) *
          ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a m * c) := by
      rw [Finset.sum_mul]
      simp_rw [← hadd]
      exact (Fintype.sum_equiv (Equiv.addRight m) _ _ (fun r => rfl)).symm
    have h2 : (∑ r, ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a r * c)) *
        (1 - ψ (_root_.GlobalTheory.HL.CharCond.rep ϖ a m * c)) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (Ne.symm hm))
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_unit_of_exact_valuation_level {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k i a : ℕ}
    (hi : a = k + i) {y : 𝒪[F]} (h1 : ϖ ^ k ∣ y) (h2 : ¬ ϖ ^ (k + 1) ∣ y) :
    ∃ u₀ : (𝒪[F])ˣ, (y : F) / (ϖ : F) ^ a * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) := by
  obtain ⟨w, rfl⟩ := h1
  have hw : ¬ ϖ ∣ w := fun h => h2 (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hu : IsUnit w := by
    by_contra hn
    apply hw
    have hmax : w ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hn
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.mem_span_singleton] at hmax
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hi]
  push_cast
  field_simp
  ring
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_filter_pow_dvd_rep_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k a : ℕ} (hk : k ≤ a)
    [Fintype (𝒪[F] ⧸ Ideal.span {ϖ ^ a})] :
    (Finset.univ.filter (fun r => ϖ ^ k ∣ _root_.GlobalTheory.HL.CharCond.rep ϖ a r)).card =
      _root_.GlobalTheory.HL.resQ ϖ ^ (a - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + k := ⟨a - k, by omega⟩
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))
  have hmem : ∀ r, ϖ ^ k ∣ _root_.GlobalTheory.HL.CharCond.rep ϖ (n + k) r ↔
      r ∈ LinearMap.range f := by
    intro r
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        Submodule.mkQ_apply]
      rw [← hy]
      exact mk_rep_eq ϖ (n + k) r
    · rintro ⟨y, rfl⟩
      have h := mk_rep_eq ϖ (n + k) (f y)
      have hfy : f y = Ideal.Quotient.mk (Ideal.span {ϖ ^ (n + k)}) (ϖ ^ k * y) := rfl
      rw [hfy, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      have h3 : ϖ ^ k ∣ _ := (pow_dvd_pow ϖ (Nat.le_add_left k n)).trans h
      have h4 : ϖ ^ k ∣ ϖ ^ k * y := dvd_mul_right _ _
      have h5 := dvd_add h3 h4
      rw [sub_add_cancel] at h5
      exact h5
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.add_sub_cancel]
  change Nat.card (LinearMap.range f) = _
  rw [← Nat.card_congr (f.quotKerEquivRange).toEquiv, ker_mkQ_comp_mulLeft_pow_eq_span hϖ n k, card_quotient_pow_eq_resQ_pow hϖ]
end GlobalTheory.HL.CharCond
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CharCond
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.CharCond
namespace _root_.GlobalTheory.HL.CharCond
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ ψ : AddChar F ℂ, (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ {U : Type} (R : Finset U) (Q : U → 𝒪[F]) (χ : U → ℂ) (a : ℕ) (B : ℕ → ℝ), (∀ i, 1 ≤ i → i ≤ a → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R, ψ (t * Q u) * χ u‖ ≤ B i) → ‖(∑ u ∈ R.filter (fun u => ϖ ^ a ∣ Q u), χ u) * (_root_.GlobalTheory.HL.resQ ϖ : ℂ) ^ a - ∑ u ∈ R, χ u‖ ≤ ∑ i ∈ Finset.Icc 1 a, ((_root_.GlobalTheory.HL.resQ ϖ : ℝ) ^ i - (_root_.GlobalTheory.HL.resQ ϖ : ℝ) ^ (i - 1)) * B i := by
  intro F _ _ _ _ ϖ hϖ ψ hψ U R Q χ a B hB
  haveI := finite_quotient_span_pow' hϖ a
  letI : Fintype (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) := Fintype.ofFinite _
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set q := _root_.GlobalTheory.HL.resQ ϖ with hqdef
  set rep := _root_.GlobalTheory.HL.CharCond.rep ϖ a with hrep
  set g : (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) → ℂ :=
    fun r => ∑ u ∈ R, ψ ((rep r : F) / (ϖ : F) ^ a * Q u) * χ u with hg
  have hcard : Fintype.card (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) = q ^ a := by
    rw [← Nat.card_eq_fintype_card, card_quotient_pow_eq_resQ_pow hϖ]
  have hsumall : ∑ r, g r = (∑ u ∈ R.filter (fun u => ϖ ^ a ∣ Q u), χ u) * (q : ℂ) ^ a := by
    have hinner : ∀ u, ∑ r, ψ ((rep r : F) / (ϖ : F) ^ a * Q u) =
        if ϖ ^ a ∣ Q u then (q : ℂ) ^ a else 0 := by
      intro u
      have hc : ((Q u : F) / (ϖ : F) ^ a) * (ϖ : F) ^ a ∈ 𝒪[F] := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hϖ0)]; exact (Q u).2
      have e := sum_addChar_rep_mul_eq_ite hψ a hc
      have hiff : ((Q u : F) / (ϖ : F) ^ a ∈ 𝒪[F]) ↔ ϖ ^ a ∣ Q u := by
        constructor
        · intro h
          refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
          push_cast
          field_simp
        · rintro ⟨w, hw⟩
          rw [hw]
          push_cast
          rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hϖ0)]
          exact w.2
      calc ∑ r, ψ ((rep r : F) / (ϖ : F) ^ a * Q u)
          = ∑ r, ψ ((rep r : F) * ((Q u : F) / (ϖ : F) ^ a)) :=
            Finset.sum_congr rfl (fun r _ => by rw [div_mul_eq_mul_div, mul_div_assoc])
        _ = _ := by
            rw [e, hcard]
            by_cases h : ϖ ^ a ∣ Q u
            · rw [if_pos (hiff.2 h), if_pos h]; push_cast; rfl
            · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
    simp only [hg]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hinner]
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    split_ifs <;> ring
  have hzero : g 0 = ∑ u ∈ R, χ u := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have h0 := mk_rep_eq ϖ a 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨w, hw⟩ := h0
    have : (rep 0 : F) / (ϖ : F) ^ a * Q u = ((w * Q u : 𝒪[F]) : F) := by
      rw [hrep, ← hw]; push_cast; field_simp
    rw [this, addChar_eq_one_of_mem_integer hψ (w * Q u).2, one_mul]
  set D : ℕ → Finset (𝒪[F] ⧸ Ideal.span {ϖ ^ a}) :=
    fun k => Finset.univ.filter (fun r => ϖ ^ k ∣ rep r) with hD
  have hDa : D a = {0} := by
    ext r
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, hrep,
      mk_rep_eq]
  have hD0 : D 0 = Finset.univ := by
    ext r; simp [hD]
  have key : ∀ j, j ≤ a → ‖∑ r ∈ D (a - j), g r - g 0‖ ≤
      ∑ i ∈ Finset.Icc 1 j, ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * B i := by
    intro j
    induction j with
    | zero => intro _; simp [hDa]
    | succ j ih =>
      intro hj
      set k := a - (j + 1) with hk
      have hkj : a - j = k + 1 := by omega
      have hsub : D (k + 1) ⊆ D k := by
        intro r hr
        simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        exact (pow_dvd_pow ϖ (Nat.le_succ k)).trans hr
      rw [hkj] at ih
      have ih' := ih (by omega)
      rw [← Finset.sum_sdiff hsub, add_sub_assoc, Finset.sum_Icc_succ_top (by omega)]
      have hlev : ∀ r ∈ D k \ D (k + 1), ‖g r‖ ≤ B (j + 1) := by
        intro r hr
        simp only [hD, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        obtain ⟨u₀, hu₀⟩ := exists_unit_of_exact_valuation_level hϖ (k := k) (i := j + 1) (a := a)
          (by omega) hr.1 hr.2
        exact hB (j + 1) (by omega) hj _ u₀ hu₀
      have hcd : ((D k \ D (k + 1)).card : ℝ) = (q : ℝ) ^ (j + 1) - (q : ℝ) ^ (j + 1 - 1) := by
        rw [Finset.card_sdiff_of_subset hsub]
        have c1 : (D k).card = q ^ (j + 1) := by
          rw [hD]; simp only; rw [card_filter_pow_dvd_rep_eq_resQ_pow hϖ (by omega)]; congr 1; omega
        have c2 : (D (k + 1)).card = q ^ j := by
          rw [hD]; simp only; rw [card_filter_pow_dvd_rep_eq_resQ_pow hϖ (by omega)]; congr 1; omega
        rw [c1, c2, Nat.add_sub_cancel]
        have : q ^ j ≤ q ^ (j + 1) :=
          Nat.pow_le_pow_right (resQ_pos_flag_measures hϖ) (Nat.le_succ j)
        push_cast [this]
        ring
      have hbound : ‖∑ r ∈ D k \ D (k + 1), g r‖ ≤
          ((q : ℝ) ^ (j + 1) - (q : ℝ) ^ (j + 1 - 1)) * B (j + 1) := by
        rw [← hcd]
        refine (norm_sum_le _ _).trans ?_
        have := Finset.sum_le_card_nsmul _ _ _ hlev
        rwa [nsmul_eq_mul] at this
      calc ‖∑ r ∈ D k \ D (k + 1), g r + (∑ r ∈ D (k + 1), g r - g 0)‖
          ≤ ‖∑ r ∈ D k \ D (k + 1), g r‖ + ‖∑ r ∈ D (k + 1), g r - g 0‖ := norm_add_le _ _
        _ ≤ _ := by linarith
  have := key a le_rfl
  rw [Nat.sub_self, hD0, hzero, hsumall] at this
  exact this
end _root_.GlobalTheory.HL.CharCond
end GlobalTheory.HL.CharCond
