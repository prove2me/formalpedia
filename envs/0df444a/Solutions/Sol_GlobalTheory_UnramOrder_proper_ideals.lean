-- Prove2me | solution 1 for GlobalTheory.UnramOrder.proper_ideals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:23.933123+00:00
-- url     : https://prove2.me/submissions/429048a0-eda5-4969-a88e-468124fe0aa2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_exists_trace
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
namespace GlobalTheory.UnramOrder
section Abstract
open IsLocalRing Polynomial
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
end Abstract
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma algebraMap_integer_mem_O' (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (a : 𝒪[F]) :
    algebraMap F E (a : F) ∈ L.O :=
  (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_inv_of_isUnit_norm (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {x : E} (hx : x ∈ L.O) {c : 𝒪[F]}
    (hc : x * L.cj x = algebraMap F E (c : F)) (hu : IsUnit c) : ∃ y ∈ L.O, x * y = 1 := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨L.cj x * algebraMap F E ((↑u⁻¹ : 𝒪[F]) : F),
    mul_mem (_root_.GlobalTheory.UnramOrder.cj_mem L hx) (algebraMap_integer_mem_O' L _), ?_⟩
  have h : ((u : 𝒪[F]) : F) * ((↑u⁻¹ : 𝒪[F]) : F) = 1 := by
    exact_mod_cast congrArg Subtype.val u.mul_inv
  rw [← mul_assoc, hc, ← map_mul, h, map_one]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma uniformizer_dvd_of_not_isUnit {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {c : 𝒪[F]}
    (hc : ¬ IsUnit c) : ∃ d, c = ϖ * d := by
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmem : c ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal c).2 hc
  rw [hmax, Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [← hd, mul_comm]⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma exists_norm_eq_uniformizer_mul_of_nonunit (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {x : E} (hx : x ∈ L.O) (hnu : ∀ z ∈ L.O, x * z ≠ 1) :
    ∃ d : 𝒪[F], x * L.cj x = algebraMap F E (ϖ : F) * algebraMap F E (d : F) := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_norm L hx
  have hcu : ¬ IsUnit c := fun hu => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_of_isUnit_norm L hx hc hu
    exact hnu y hy hxy
  obtain ⟨d, rfl⟩ := uniformizer_dvd_of_not_isUnit hϖ hcu
  exact ⟨d, by rw [hc, MulMemClass.coe_mul, map_mul]⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma cj_algebraMap' (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (a : F) :
    L.cj (algebraMap F E a) = algebraMap F E a :=
  L.cj.commutes a
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_norm_eq_uniformizer' (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O)
    (hnorm : ∀ u : 𝒪[F]ˣ, ∃ x ∈ L.O, x * L.cj x = algebraMap F E ((u : 𝒪[F]) : F))
    {y : E} (hy : y ∈ L.O) (hyu : ∀ z ∈ L.O, y * z ≠ 1)
    (hyϖ : ∀ c ∈ L.O, y ≠ algebraMap F E (ϖ : F) * c) :
    ∃ π ∈ L.O, π * L.cj π = algebraMap F E (ϖ : F) := by
  haveI := hPID
  let y₁ : L.O := ⟨y, hy⟩
  let ϖ₁ : L.O := ⟨algebraMap F E (ϖ : F), algebraMap_integer_mem_O' L ϖ⟩
  let J : Ideal L.O := Ideal.span {y₁, ϖ₁}
  obtain ⟨p, hp⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator J).1
    (Ideal.subset_span (by simp) : y₁ ∈ J)
  obtain ⟨t, ht⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator J).1
    (Ideal.subset_span (by simp) : ϖ₁ ∈ J)
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (Submodule.IsPrincipal.generator_mem J)
  set g := Submodule.IsPrincipal.generator J
  have hpE : y = (p : E) * g := by simpa [y₁, smul_eq_mul] using congrArg Subtype.val hp
  have htE : algebraMap F E (ϖ : F) = (t : E) * g := by
    simpa [ϖ₁, smul_eq_mul] using congrArg Subtype.val ht
  have habE : (a : E) * y + b * algebraMap F E (ϖ : F) = g := by
    simpa [y₁, ϖ₁] using congrArg Subtype.val hab
  have hg : ∀ z ∈ L.O, (g : E) * z ≠ 1 := by
    intro z hz hgz
    obtain ⟨d, hd⟩ := exists_norm_eq_uniformizer_mul_of_nonunit L hϖ hy hyu
    have hmem : algebraMap F E (d : F) * a * z + b * z * L.cj y ∈ L.O :=
      add_mem (mul_mem (mul_mem (algebraMap_integer_mem_O' L d) a.2) hz)
        (mul_mem (mul_mem b.2 hz) (_root_.GlobalTheory.UnramOrder.cj_mem L hy))
    have hσy : L.cj y = algebraMap F E (ϖ : F) *
        (algebraMap F E (d : F) * a * z + b * z * L.cj y) := by
      linear_combination (-L.cj y) * hgz + (-(L.cj y) * z) * habE + ((a : E) * z) * hd
    refine hyϖ _ (_root_.GlobalTheory.UnramOrder.cj_mem L hmem) ?_
    have := congrArg L.cj hσy
    rwa [L.cj_cj, map_mul, cj_algebraMap'] at this
  have ht' : ∀ z ∈ L.O, (t : E) * z ≠ 1 := by
    intro z hz htz
    refine hyϖ ((p : E) * z) (mul_mem p.2 hz) ?_
    linear_combination hpE - ((p : E) * z) * htE - ((p : E) * g) * htz
  obtain ⟨d₁, hd₁⟩ := exists_norm_eq_uniformizer_mul_of_nonunit L hϖ g.2 hg
  obtain ⟨d₂, hd₂⟩ := exists_norm_eq_uniformizer_mul_of_nonunit L hϖ t.2 ht'
  have hE : algebraMap F E ((ϖ : F) * ϖ * 1) = algebraMap F E ((ϖ : F) * ϖ * (d₁ * d₂)) := by
    simp only [map_mul, map_one]
    calc algebraMap F E (ϖ : F) * algebraMap F E (ϖ : F) * 1
        = ((t : E) * g) * L.cj ((t : E) * g) := by rw [← htE, cj_algebraMap', mul_one]
      _ = ((t : E) * L.cj t) * ((g : E) * L.cj g) := by rw [map_mul]; ring
      _ = _ := by rw [hd₁, hd₂]; ring
  have hϖ0 : (ϖ : F) * ϖ ≠ 0 := by
    have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    exact mul_ne_zero h0 h0
  have hdF : (1 : F) = d₁ * d₂ := mul_left_cancel₀ hϖ0 (_root_.GlobalTheory.UnramOrder.algebraMap_inj L hE)
  have hd : d₁ * d₂ = 1 := Subtype.ext (by rw [MulMemClass.coe_mul]; exact hdF.symm)
  obtain ⟨z, hz, hzN⟩ := hnorm ⟨d₂, d₁, by rw [mul_comm]; exact hd, hd⟩
  refine ⟨g * z, mul_mem g.2 hz, ?_⟩
  have hdd : algebraMap F E (d₁ : F) * algebraMap F E (d₂ : F) = 1 := by
    rw [← map_mul, ← hdF, map_one]
  calc (g * z : E) * L.cj (g * z) = ((g : E) * L.cj g) * (z * L.cj z) := by rw [map_mul]; ring
    _ = _ := by
      rw [hd₁, hzN]
      linear_combination (algebraMap F E (ϖ : F)) * hdd
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma isUnit_algebraMap_uniformizer (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    IsUnit (algebraMap F E (ϖ : F)) := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  exact (IsUnit.mk0 _ h0).map _
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_coprime_combination_pi_cj (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O) {π : E} (hπ : π ∈ L.O)
    (hN : π * L.cj π = algebraMap F E (ϖ : F)) :
    ∃ r ∈ L.O, ∃ s ∈ L.O, π * r + L.cj π * s = 1 := by
  haveI := hPID
  let π₁ : L.O := ⟨π, hπ⟩
  let π₂ : L.O := ⟨L.cj π, _root_.GlobalTheory.UnramOrder.cj_mem L hπ⟩
  let K : Ideal L.O := Ideal.span {π₁, π₂}
  obtain ⟨p, hp⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator K).1
    (Ideal.subset_span (by simp) : π₁ ∈ K)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator K).1
    (Ideal.subset_span (by simp) : π₂ ∈ K)
  set δ := Submodule.IsPrincipal.generator K
  have hp' : π = (p : E) * δ := by simpa [π₁, smul_eq_mul] using congrArg Subtype.val hp
  have hq' : L.cj π = (q : E) * δ := by simpa [π₂, smul_eq_mul] using congrArg Subtype.val hq
  have hsq : ((δ : E) * p * q) * ((δ : E) * p * q) = algebraMap F E (ϖ : F) * ((p : E) * q) := by
    rw [← hN, hq', hp']; ring
  have hspan : ((p * q : L.O) : E) • algebraMap F E (ϖ : F) = (δ : E) * p * q * ((δ : E) * p * q) := by
    rw [hsq, smul_eq_mul, Subring.coe_mul, mul_comm]
  have hmem := L.unram ϖ hϖ _ (mul_mem (mul_mem δ.2 p.2) q.2)
    (Submodule.mem_span_singleton.2 ⟨p * q, by rw [Subring.smul_def]; exact hspan⟩)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  rw [Subring.smul_def, smul_eq_mul] at ha
  have hu : IsUnit ((δ : E) * p * q) := by
    apply isUnit_of_mul_isUnit_left (y := (δ : E))
    rw [show (δ : E) * p * q * δ = algebraMap F E (ϖ : F) by rw [← hN, hq', hp']; ring]
    exact isUnit_algebraMap_uniformizer L hϖ
  have h1 : (a : E) * δ = 1 := by
    have : ((δ : E) * p * q) * ((a : E) * δ) = ((δ : E) * p * q) * 1 := by
      rw [mul_one]
      calc ((δ : E) * p * q) * ((a : E) * δ) = (a : E) * (((p : E) * δ) * ((q : E) * δ)) := by ring
        _ = _ := by rw [← hp', ← hq', hN, ha]
    exact hu.mul_left_cancel this
  have hδ : IsUnit δ := isUnit_iff_exists_inv'.2 ⟨a, Subtype.ext (by simpa using h1)⟩
  have hK : K = ⊤ := by
    rw [← Submodule.IsPrincipal.span_singleton_generator K]
    exact Ideal.span_singleton_eq_top.2 hδ
  have h1K : (1 : L.O) ∈ K := hK ▸ Submodule.mem_top
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 h1K
  refine ⟨r, r.2, s, s.2, ?_⟩
  have := congrArg Subtype.val hrs
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_one, π₁, π₂] at this
  linear_combination this
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma exists_mul_eq_one_add_pi_mul_of_not_dvd (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O) {π : E} (hπ : π ∈ L.O)
    (hN : π * L.cj π = algebraMap F E (ϖ : F)) {x : E} (hx : x ∈ L.O)
    (hnot : ¬ ∃ c ∈ L.O, x = π * c) : ∃ u ∈ L.O, ∃ w ∈ L.O, x * u = 1 + π * w := by
  obtain ⟨r, hr, s, hs, hrs⟩ := exists_coprime_combination_pi_cj L hϖ hPID hπ hN
  have hσπ := _root_.GlobalTheory.UnramOrder.cj_mem L hπ
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L (mul_mem hx (mul_mem hσπ hs))
  have hcj : L.cj (x * (L.cj π * s)) = L.cj x * π * L.cj s := by
    rw [map_mul, map_mul, L.cj_cj]; ring
  have hwO : x * r - L.cj x * L.cj s ∈ L.O :=
    sub_mem (mul_mem hx hr)
      (mul_mem (_root_.GlobalTheory.UnramOrder.cj_mem L hx) (_root_.GlobalTheory.UnramOrder.cj_mem L hs))
  have hxa : x = algebraMap F E (a : F) + π * (x * r - L.cj x * L.cj s) := by
    rw [← ha, hcj]; linear_combination (-x) * hrs
  have hau : IsUnit a := by
    by_contra hna
    obtain ⟨d, rfl⟩ := uniformizer_dvd_of_not_isUnit hϖ hna
    refine hnot ⟨L.cj π * algebraMap F E (d : F) + (x * r - L.cj x * L.cj s),
      add_mem (mul_mem hσπ (algebraMap_integer_mem_O' L d)) hwO, ?_⟩
    calc x = _ := hxa
      _ = _ := by rw [MulMemClass.coe_mul, map_mul, ← hN]; ring
  obtain ⟨v, rfl⟩ := hau
  have hv : algebraMap F E ((v : 𝒪[F]) : F) * algebraMap F E ((↑v⁻¹ : 𝒪[F]) : F) = 1 := by
    rw [← map_mul, show ((v : 𝒪[F]) : F) * ((↑v⁻¹ : 𝒪[F]) : F) = 1 by
      exact_mod_cast congrArg Subtype.val v.mul_inv, map_one]
  refine ⟨algebraMap F E ((↑v⁻¹ : 𝒪[F]) : F), algebraMap_integer_mem_O' L _,
    (x * r - L.cj x * L.cj s) * algebraMap F E ((↑v⁻¹ : 𝒪[F]) : F),
    mul_mem hwO (algebraMap_integer_mem_O' L _), ?_⟩
  conv_lhs => rw [hxa]
  linear_combination hv
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma exists_inv_one_sub_uniformizer_mul (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {w : E} (hw : w ∈ L.O) :
    ∃ y ∈ L.O, (1 - algebraMap F E (ϖ : F) * w) * y = 1 := by
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L hw
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramOrder.exists_norm L hw
  apply exists_inv_of_isUnit_norm L
    (sub_mem (one_mem _) (mul_mem (algebraMap_integer_mem_O' L ϖ) hw)) (c := 1 - ϖ * (t - ϖ * n))
  · rw [map_sub, map_mul, cj_algebraMap', map_one,
      show ((1 - ϖ * (t - ϖ * n) : 𝒪[F]) : F) = 1 - (ϖ : F) * ((t : F) - ϖ * n) by push_cast; ring]
    simp only [map_sub, map_mul, map_one]
    linear_combination (-algebraMap F E (ϖ : F)) * ht + (algebraMap F E (ϖ : F)) ^ 2 * hn
  · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ϖ * (t - ϖ * n)) with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) hϖ.not_isUnit
    · exact h
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma ideal_le_pi_or_le_cj_pi_of_proper (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (hPID : IsPrincipalIdealRing L.O) {π : E} (hπ : π ∈ L.O)
    (hN : π * L.cj π = algebraMap F E (ϖ : F)) (I : Ideal L.O) (hI : I ≠ ⊤) :
    (∀ x ∈ I, ∃ c ∈ L.O, (x : E) = π * c) ∨ ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = L.cj π * c := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x₁, hx₁I, hx₁⟩, ⟨x₂, hx₂I, hx₂⟩⟩ := hcon
  have hN' : L.cj π * L.cj (L.cj π) = algebraMap F E (ϖ : F) := by rw [L.cj_cj, mul_comm, hN]
  obtain ⟨u₁, hu₁, w₁, hw₁, h₁⟩ := exists_mul_eq_one_add_pi_mul_of_not_dvd L hϖ hPID hπ hN x₁.2
    (by rintro ⟨c, hc, h⟩; exact hx₁ c hc h)
  obtain ⟨u₂, hu₂, w₂, hw₂, h₂⟩ := exists_mul_eq_one_add_pi_mul_of_not_dvd L hϖ hPID
    (_root_.GlobalTheory.UnramOrder.cj_mem L hπ) hN' x₂.2 (by rintro ⟨c, hc, h⟩; exact hx₂ c hc h)
  obtain ⟨y, hy, hy1⟩ := exists_inv_one_sub_uniformizer_mul L hϖ (mul_mem hw₁ hw₂)
  let z : L.O := x₁ * ⟨u₁, hu₁⟩ + x₂ * ⟨u₂, hu₂⟩ - x₁ * ⟨u₁, hu₁⟩ * x₂ * ⟨u₂, hu₂⟩
  have hz : z ∈ I := sub_mem (add_mem (I.mul_mem_right _ hx₁I) (I.mul_mem_right _ hx₂I))
    (I.mul_mem_right _ (I.mul_mem_left _ hx₂I))
  have hzE : (z : E) = 1 - algebraMap F E (ϖ : F) * (w₁ * w₂) := by
    rw [show (z : E) = (x₁ : E) * u₁ + x₂ * u₂ - x₁ * u₁ * x₂ * u₂ from rfl]
    linear_combination (1 - (x₂ : E) * u₂) * h₁ + (-(π * w₁)) * h₂ + (-(w₁ * w₂)) * hN
  apply hI
  refine Ideal.eq_top_of_isUnit_mem I hz (isUnit_iff_exists_inv.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
  show (z : E) * y = 1
  rw [hzE, hy1]
end GlobalTheory.UnramOrder
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.UnramOrder
namespace _root_.GlobalTheory.UnramOrder
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ →
    (∀ I : Ideal L.O, I ≠ ⊤ → ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = algebraMap F E ϖ * c) ∨
    ∃ π ∈ L.O, π * L.cj π = algebraMap F E ϖ ∧ ∀ I : Ideal L.O, I ≠ ⊤ →
      (∀ x ∈ I, ∃ c ∈ L.O, (x : E) = π * c) ∨ ∀ x ∈ I, ∃ c ∈ L.O, (x : E) = L.cj π * c := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  obtain ⟨-, -, -, hPID, -, -, -, hnorm⟩ := _root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  by_cases h : ∃ y ∈ L.O, (∀ z ∈ L.O, y * z ≠ 1) ∧ ∀ c ∈ L.O, y ≠ algebraMap F E ϖ * c
  · right
    obtain ⟨y, hy, hyu, hyϖ⟩ := h
    obtain ⟨π, hπ, hN⟩ := exists_norm_eq_uniformizer' L hϖ hPID hnorm hy hyu hyϖ
    exact ⟨π, hπ, hN, fun I hI => ideal_le_pi_or_le_cj_pi_of_proper L hϖ hPID hπ hN I hI⟩
  · left
    push_neg at h
    intro I hI x hx
    apply h x x.2
    intro z hz hxz
    exact hI (Ideal.eq_top_of_isUnit_mem I hx (isUnit_iff_exists_inv.2 ⟨⟨z, hz⟩, Subtype.ext hxz⟩))
end _root_.GlobalTheory.UnramOrder
end GlobalTheory.UnramOrder
