-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2a6507c6-e013-58a4-9c08-223fb4897104

import Definitions.Def_ModularCurve_ChartSemicontinuity
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst.AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord_zero algebraAlong isScalarTower_along isIntegral_along Place.ramificationIndexAlong Place.ord_restrictAlong"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow algebraMap_mem' toValuationSubring restrictAlong ramificationIndexAlong ord_restrictAlong ramificationIndex ramificationIndex_le_ord ramificationIndex_pos ord_nonneg_of_mem mem_iff_ord_nonneg"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
section PlaceGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.vb_hasValue_add {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) :
    v.HasValue (f + g) (a + b) := by
  obtain ⟨hfm, hfr⟩ := hf
  obtain ⟨hgm, hgr⟩ := hg
  refine ⟨add_mem hfm hgm, ?_⟩
  have hx : (⟨f + g, add_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ + ⟨g, hgm⟩ := rfl
  rw [hx, map_add, hfr, hgr, map_add]

p2m_export "AlgebraicCurve.Place" "vb_hasValue_add"
private theorem _root_.AlgebraicCurve.Place.vb_hasValue_neg {f : F} {a : K} (hf : v.HasValue f a) : v.HasValue (-f) (-a) := by
  obtain ⟨hfm, hfr⟩ := hf
  refine ⟨neg_mem hfm, ?_⟩
  have hx : (⟨-f, neg_mem hfm⟩ : v.toValuationSubring) = -⟨f, hfm⟩ := rfl
  rw [hx, map_neg, hfr, map_neg]

p2m_export "AlgebraicCurve.Place" "vb_hasValue_neg"
private theorem _root_.AlgebraicCurve.Place.vb_hasValue_zero : v.HasValue (0 : F) 0 := by
  simpa using v.hasValue_algebraMap (0 : K)

p2m_export "AlgebraicCurve.Place" "vb_hasValue_zero"

private theorem _root_.AlgebraicCurve.Place.vb_hasValue_zero_iff_mem_maximalIdeal {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValue f 0 ↔ (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  constructor
  · rintro ⟨hf', hr⟩
    rw [map_zero] at hr
    exact (IsLocalRing.residue_eq_zero_iff _).mp hr
  · intro hm
    exact ⟨hf, by rw [map_zero]; exact (IsLocalRing.residue_eq_zero_iff _).mpr hm⟩

p2m_export "AlgebraicCurve.Place" "vb_hasValue_zero_iff_mem_maximalIdeal"

theorem vb_not_mem_maximalIdeal_of_hasValue {f : F} {a : K} (h : v.HasValue f a) (ha : a ≠ 0) :
    (⟨f, h.mem⟩ : v.toValuationSubring) ∉ IsLocalRing.maximalIdeal v.toValuationSubring := fun hm =>
  ha ((h.unique ((v.vb_hasValue_zero_iff_mem_maximalIdeal h.mem).mpr hm)))

private theorem _root_.AlgebraicCurve.Place.vb_ord_irreducible_pow_mul_unit {π : v.toValuationSubring} (hπ : Irreducible π) (n : ℕ)
    {u : v.toValuationSubring} (hu : IsUnit u) :
    v.ord ((π : F) ^ n * (u : F)) = n := by
  have h := v.ord_unit_smul_zpow hu.unit hπ (n : ℤ)
  rw [IsUnit.unit_spec, zpow_natCast] at h
  rw [mul_comm]
  exact h

p2m_export "AlgebraicCurve.Place" "vb_ord_irreducible_pow_mul_unit"

private theorem _root_.AlgebraicCurve.Place.vb_le_ord_of_pow_dvd {π : v.toValuationSubring} (hπ : Irreducible π) {n : ℕ}
    {x : v.toValuationSubring} (hx : (x : F) ≠ 0) (h : π ^ n ∣ x) : (n : ℤ) ≤ v.ord (x : F) := by
  obtain ⟨y, hy⟩ := h
  have hy0 : (y : F) ≠ 0 := by
    intro h0
    apply hx
    rw [hy]
    push_cast
    rw [h0, mul_zero]
  have hπ0 : ((π : F) ^ n) ≠ 0 := pow_ne_zero _ (by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero)
  rw [hy]
  push_cast
  rw [v.ord_mul hπ0 hy0, ← zpow_natCast, v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
  have := v.ord_nonneg_of_mem y.2
  omega

p2m_export "AlgebraicCurve.Place" "vb_le_ord_of_pow_dvd"

theorem vb_pow_dvd_of_le_ord {π : v.toValuationSubring} (hπ : Irreducible π) {n : ℕ}
    {x : v.toValuationSubring} (h : (n : ℤ) ≤ v.ord (x : F)) : π ^ n ∣ x := by
  by_cases hx : (x : F) = 0
  · have : x = 0 := Subtype.ext hx
    rw [this]
    exact dvd_zero _
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := x) (fun h0 => hx (by rw [h0]; rfl)) hπ
  have hord : v.ord (x : F) = m := by
    have h1 := congrArg Subtype.val hu
    push_cast at h1
    rw [h1, mul_comm]
    exact v.vb_ord_irreducible_pow_mul_unit hπ m u.isUnit
  rw [hord] at h
  have hnm : n ≤ m := by exact_mod_cast h
  rw [hu]
  exact Dvd.dvd.mul_left (pow_dvd_pow π hnm) _

theorem vb_one_le_ord_of_mem_maximalIdeal {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    1 ≤ v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have := v.vb_le_ord_of_pow_dvd hπ (n := 1) (x := ⟨f, hf⟩) hf0 (by rwa [pow_one])
  exact_mod_cast this

theorem vb_ord_eq_one_of_eq_irreducible_mul {π : v.toValuationSubring} (hπ : Irreducible π)
    {x w : v.toValuationSubring} (hw : IsUnit w) (h : x = π * w) : v.ord (x : F) = 1 := by
  have := v.vb_ord_irreducible_pow_mul_unit hπ 1 hw
  rw [pow_one] at this
  rw [h]
  push_cast
  exact this

end PlaceGeneric
end AlgebraicCurve.Place

namespace VbUnrq

section Chart

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
  {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}

theorem closure_le_integers (hS : IsChartAt R v S) :
    ∀ s ∈ Subring.closure S, s ∈ R.R₁.integers := fun s hs =>
  (Subring.closure_le (t := R.R₁.integers.toSubring)).mpr (fun x hx => hS.integral x hx) hs

theorem closure_le_place (hS : IsChartAt R v S)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hWv : P.reduceFst W = v) :
    ∀ s ∈ Subring.closure S, s ∈ W.toValuationSubring := fun s hs =>
  (Subring.closure_le (t := W.toValuationSubring.toSubring)).mpr (fun x hx => hS.regularOver x hx W hWv) hs

theorem residue_closure_mem (hS : IsChartAt R v S) {s : modularFunctionFieldBar (N * q)}
    (hs : s ∈ Subring.closure S) :
    (R.residue₁ ⟨s, closure_le_integers hS s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring := by
  induction hs using Subring.closure_induction with
  | mem x hx => exact hS.regular x hx
  | zero =>
    have : (⟨(0 : modularFunctionFieldBar (N * q)), closure_le_integers hS _ (zero_mem _)⟩ : R.R₁.integers) = 0 := rfl
    rw [this, map_zero]; exact zero_mem _
  | one =>
    have : (⟨(1 : modularFunctionFieldBar (N * q)), closure_le_integers hS _ (one_mem _)⟩ : R.R₁.integers) = 1 := rfl
    rw [this, map_one]; exact one_mem _
  | add x y hx hy ihx ihy =>
    have : (⟨x + y, closure_le_integers hS _ (add_mem hx hy)⟩ : R.R₁.integers) =
        ⟨x, closure_le_integers hS _ hx⟩ + ⟨y, closure_le_integers hS _ hy⟩ := rfl
    rw [this, map_add]; exact add_mem ihx ihy
  | neg x hx ihx =>
    have : (⟨-x, closure_le_integers hS _ (neg_mem hx)⟩ : R.R₁.integers) =
        -⟨x, closure_le_integers hS _ hx⟩ := rfl
    rw [this, map_neg]; exact neg_mem ihx
  | mul x y hx hy ihx ihy =>
    have : (⟨x * y, closure_le_integers hS _ (mul_mem hx hy)⟩ : R.R₁.integers) =
        ⟨x, closure_le_integers hS _ hx⟩ * ⟨y, closure_le_integers hS _ hy⟩ := rfl
    rw [this, map_mul]; exact mul_mem ihx ihy

set_option maxHeartbeats 4000000 in

theorem valueLaw_closure (hS : IsChartAt R v S)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v)
    {s : modularFunctionFieldBar (N * q)} (hs : s ∈ Subring.closure S) :
    ∃ a : A, W.HasValue s (a : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨s, closure_le_integers hS s hs⟩) (red a) := by
  induction hs using Subring.closure_induction with
  | mem x hx => exact hS.valueLaw x hx W hW hWv
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · rw [ZeroMemClass.coe_zero]; exact W.vb_hasValue_zero
    · have : (⟨(0 : modularFunctionFieldBar (N * q)), closure_le_integers hS _ (zero_mem _)⟩ : R.R₁.integers) = 0 := rfl
      rw [this, map_zero, map_zero]; exact v.vb_hasValue_zero
  | one =>
    refine ⟨1, ?_, ?_⟩
    · rw [OneMemClass.coe_one]; exact W.hasValue_one
    · have : (⟨(1 : modularFunctionFieldBar (N * q)), closure_le_integers hS _ (one_mem _)⟩ : R.R₁.integers) = 1 := rfl
      rw [this, map_one, map_one]; exact v.hasValue_one
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha, ha'⟩ := ihx
    obtain ⟨b, hb, hb'⟩ := ihy
    refine ⟨a + b, ?_, ?_⟩
    · rw [AddMemClass.coe_add]; exact W.vb_hasValue_add ha hb
    · have : (⟨x + y, closure_le_integers hS _ (add_mem hx hy)⟩ : R.R₁.integers) =
          ⟨x, closure_le_integers hS _ hx⟩ + ⟨y, closure_le_integers hS _ hy⟩ := rfl
      rw [this, map_add, map_add]; exact v.vb_hasValue_add ha' hb'
  | neg x hx ihx =>
    obtain ⟨a, ha, ha'⟩ := ihx
    refine ⟨-a, ?_, ?_⟩
    · rw [NegMemClass.coe_neg]; exact W.vb_hasValue_neg ha
    · have : (⟨-x, closure_le_integers hS _ (neg_mem hx)⟩ : R.R₁.integers) =
          -⟨x, closure_le_integers hS _ hx⟩ := rfl
      rw [this, map_neg, map_neg]; exact v.vb_hasValue_neg ha'
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha, ha'⟩ := ihx
    obtain ⟨b, hb, hb'⟩ := ihy
    refine ⟨a * b, ?_, ?_⟩
    · rw [MulMemClass.coe_mul]; exact ha.mul hb
    · have : (⟨x * y, closure_le_integers hS _ (mul_mem hx hy)⟩ : R.R₁.integers) =
          ⟨x, closure_le_integers hS _ hx⟩ * ⟨y, closure_le_integers hS _ hy⟩ := rfl
      rw [this, map_mul, map_mul]; exact ha'.mul hb'

theorem eval_derivative_map_mem_closure
    (z : modularFunctionFieldBar (N * q)) (hz : z ∈ Subring.closure S)
    (m : Polynomial (modularFunctionFieldBar N))
    (hm : ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ Subring.closure S) :
    (Polynomial.derivative (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)).eval z
      ∈ Subring.closure S := by
  rw [Polynomial.eval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ hz _)
  rw [Polynomial.coeff_derivative, Polynomial.coeff_map]
  refine Subring.mul_mem _ ?_ ?_
  · exact hm (i + 1)
  · exact_mod_cast natCast_mem (Subring.closure S) (i + 1)

theorem eval_map_mem_closure
    (z : modularFunctionFieldBar (N * q)) (hz : z ∈ Subring.closure S)
    (m : Polynomial (modularFunctionFieldBar N))
    (hm : ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ Subring.closure S) :
    (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z ∈ Subring.closure S := by
  rw [Polynomial.eval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ hz _)
  rw [Polynomial.coeff_map]
  exact hm i

theorem isUnit_of_red_ne_zero {A' : ValuationSubring (AlgebraicClosure ℚ)} {k' : Type*} [Field k']
    (p : ℕ) [Fact p.Prime] [CharP k' p] (red' : A' →+* k') {a : A'} (ha : red' a ≠ 0) : IsUnit a := by
  by_contra h
  exact ha (ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A' p red'
    ((IsLocalRing.mem_maximalIdeal a).mpr h))

theorem mem_maximalIdeal_of_red_eq_zero {A' : ValuationSubring (AlgebraicClosure ℚ)} {k' : Type*} [Field k']
    (red' : A' →+* k') {a : A'} (ha : red' a = 0) : a ∈ IsLocalRing.maximalIdeal A' := by
  have hker : RingHom.ker red' ≠ ⊤ := RingHom.ker_ne_top red'
  exact IsLocalRing.le_maximalIdeal hker ha

theorem exists_hasValue_ne_zero_of_etale (hS : IsChartAt R v S)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v)
    {s : modularFunctionFieldBar (N * q)} (hs : s ∈ Subring.closure S)
    (hunit : ∀ h : s ∈ R.R₁.integers, ¬ v.HasValue (R.residue₁ ⟨s, h⟩) (0 : k)) :
    ∃ a : A, IsUnit a ∧ W.HasValue s (a : AlgebraicClosure ℚ) := by
  obtain ⟨a, ha, ha'⟩ := valueLaw_closure hS hW hWv hs
  refine ⟨a, isUnit_of_red_ne_zero q red fun h0 => ?_, ha⟩
  rw [h0] at ha'
  exact hunit _ ha'

end Chart

end VbUnrq

namespace VbUnrq

section Newton

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

noncomputable def newtonStep (m : Polynomial F) (c : F) : F :=
  c - m.eval c / (Polynomial.derivative m).eval c

noncomputable def newtonSeq (m : Polynomial F) (c₀ : F) : ℕ → F
  | 0 => c₀
  | n + 1 => newtonStep m (newtonSeq m c₀ n)

variable (φ : F →ₐ[K] F') (W : Place K F') (m : Polynomial F) (z : F')

structure NewtonData : Prop where
  z_mem : z ∈ W.toValuationSubring
  coeff_mem : ∀ i : ℕ, φ (m.coeff i) ∈ W.toValuationSubring
  root : (m.map φ.toRingHom).eval z = 0
  unit : ∃ a : K, a ≠ 0 ∧ W.HasValue ((Polynomial.derivative (m.map φ.toRingHom)).eval z) a

variable {φ W m z}

theorem NewtonData.exists_lift (h : NewtonData φ W m z) :
    ∃ mO : Polynomial W.toValuationSubring, mO.map W.toValuationSubring.subtype = m.map φ.toRingHom := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_map]
  exact ⟨⟨φ (m.coeff n), h.coeff_mem n⟩, rfl⟩

theorem eval_map_coe (mO : Polynomial W.toValuationSubring) (x : W.toValuationSubring) :
    ((mO.eval x : W.toValuationSubring) : F') = (mO.map W.toValuationSubring.subtype).eval (x : F') := by
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_hom W.toValuationSubring.subtype x).symm

theorem eval_map_apply (m : Polynomial F) (c : F) :
    (m.map φ.toRingHom).eval (φ c) = φ (m.eval c) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_hom φ.toRingHom c

theorem isUnit_of_sub_mem {O : Type*} [CommRing O] [IsLocalRing O] {e e₀ : O} (he₀ : IsUnit e₀)
    (h : e - e₀ ∈ IsLocalRing.maximalIdeal O) : IsUnit e := by
  by_contra hne
  have he : e ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal e).mpr hne
  have : e₀ ∈ IsLocalRing.maximalIdeal O := by
    have := Ideal.sub_mem _ he h
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.mem_maximalIdeal e₀).mp this he₀

theorem NewtonData.step (h : NewtonData φ W m z) {π : W.toValuationSubring} (hπ : Irreducible π)
    {c : F} (hc : φ c ∈ W.toValuationSubring) {r : ℕ} (hr : 1 ≤ r)
    (hdiv : π ^ r ∣ (⟨z, h.z_mem⟩ - ⟨φ c, hc⟩ : W.toValuationSubring)) :
    ∃ hc' : φ (newtonStep m c) ∈ W.toValuationSubring,
      π ^ (2 * r) ∣ (⟨z, h.z_mem⟩ - ⟨φ (newtonStep m c), hc'⟩ : W.toValuationSubring) := by
  obtain ⟨mO, hmO⟩ := h.exists_lift
  set z' : W.toValuationSubring := ⟨z, h.z_mem⟩ with hz'
  set x : W.toValuationSubring := ⟨φ c, hc⟩ with hx
  set y : W.toValuationSubring := z' - x with hy

  have hroot : mO.eval z' = 0 := by
    apply Subtype.ext
    rw [eval_map_coe, hmO]
    exact h.root

  have hunitz : IsUnit ((Polynomial.derivative mO).eval z') := by
    obtain ⟨a, ha0, ha⟩ := h.unit
    have hmem := ha.mem
    have hcoe : (((Polynomial.derivative mO).eval z' : W.toValuationSubring) : F') =
        (Polynomial.derivative (m.map φ.toRingHom)).eval z := by
      rw [eval_map_coe, ← Polynomial.derivative_map, hmO]
    have : (Polynomial.derivative mO).eval z' = ⟨_, hmem⟩ := Subtype.ext hcoe
    rw [this]
    exact ha.isUnit ha0

  set e : W.toValuationSubring := (Polynomial.derivative mO).eval x with he
  have hxz : π ∣ x - z' := by
    have h1 : π ∣ π ^ r := dvd_pow_self π (by omega)
    have h2 : π ∣ z' - x := h1.trans hdiv
    rw [← neg_sub]
    exact (dvd_neg).mpr h2
  have hunit : IsUnit e := by
    refine isUnit_of_sub_mem hunitz ?_
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact hxz.trans (Polynomial.sub_dvd_eval_sub x z' _)

  obtain ⟨kk, hk⟩ := Polynomial.binomExpansion mO x y
  rw [← he] at hk
  have hxy : x + y = z' := by rw [hy]; abel
  rw [hxy, hroot] at hk

  obtain ⟨w, hw⟩ : ∃ w : W.toValuationSubring, e * w = 1 := ⟨↑(hunit.unit⁻¹), by rw [IsUnit.mul_val_inv]⟩
  have he0 : (e : F') ≠ 0 := by
    intro h0
    have := congrArg Subtype.val hw
    push_cast at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hwinv : (w : F') = (e : F')⁻¹ := by
    have := congrArg Subtype.val hw
    push_cast at this
    exact (eq_inv_of_mul_eq_one_right this)

  have hstep : φ (newtonStep m c) = ((z' + w * kk * y ^ 2 : W.toValuationSubring) : F') := by
    have hA : φ (m.eval c) = ((mO.eval x : W.toValuationSubring) : F') := by
      rw [eval_map_coe, hmO]
      exact (eval_map_apply m c).symm
    have hB : φ ((Polynomial.derivative m).eval c) = ((e : W.toValuationSubring) : F') := by
      rw [he, eval_map_coe, ← Polynomial.derivative_map, hmO, Polynomial.derivative_map]
      exact (eval_map_apply (Polynomial.derivative m) c).symm
    have h1 : φ (newtonStep m c) = (x : F') - ((mO.eval x : W.toValuationSubring) : F') / (e : F') := by
      rw [newtonStep, map_sub, map_div₀, hA, hB]
    have h2 : ((mO.eval x : W.toValuationSubring) : F') = -((e : F') * y + kk * y ^ 2) := by
      have := congrArg Subtype.val hk
      push_cast at this ⊢
      linear_combination -this
    rw [h1, h2]
    push_cast
    rw [hwinv]
    field_simp
    have : (x : F') + (y : F') = (z' : F') := by rw [← hxy]; push_cast; ring
    linear_combination (e : F') * this
  refine ⟨by rw [hstep]; exact SetLike.coe_mem _, ?_⟩
  have hmem : (⟨φ (newtonStep m c), by rw [hstep]; exact SetLike.coe_mem _⟩ : W.toValuationSubring) = z' + w * kk * y ^ 2 :=
    Subtype.ext hstep
  rw [hmem, show z' - (z' + w * kk * y ^ 2) = -(w * kk) * y ^ 2 by ring]
  refine Dvd.dvd.mul_left ?_ _
  rw [pow_mul', sq, sq]
  exact mul_dvd_mul hdiv hdiv

theorem NewtonData.seq (h : NewtonData φ W m z) {π : W.toValuationSubring} (hπ : Irreducible π)
    {c₀ : F} (hc₀ : φ c₀ ∈ W.toValuationSubring)
    (hdiv₀ : π ∣ (⟨z, h.z_mem⟩ - ⟨φ c₀, hc₀⟩ : W.toValuationSubring)) (n : ℕ) :
    ∃ hc : φ (newtonSeq m c₀ n) ∈ W.toValuationSubring,
      π ^ (2 ^ n) ∣ (⟨z, h.z_mem⟩ - ⟨φ (newtonSeq m c₀ n), hc⟩ : W.toValuationSubring) := by
  induction n with
  | zero => exact ⟨hc₀, by simpa [newtonSeq] using hdiv₀⟩
  | succ n ih =>
    obtain ⟨hc, hd⟩ := ih
    obtain ⟨hc', hd'⟩ := h.step hπ hc (Nat.one_le_two_pow) hd
    refine ⟨hc', ?_⟩
    rw [pow_succ, mul_comm]
    exact hd'

end Newton

end VbUnrq

namespace VbUnrq

section Approx

variable {K F' : Type*} [Field K] [Field F'] [Algebra K F'] (W : Place K F')

theorem ord_eval_eq_of_pow_dvd {π : W.toValuationSubring} (hπ : Irreducible π)
    (qO : Polynomial W.toValuationSubring) {z' x : W.toValuationSubring} {M : ℕ}
    (hdiv : π ^ M ∣ z' - x) (h0 : ((qO.eval z' : W.toValuationSubring) : F') ≠ 0)
    (hlt : W.ord ((qO.eval z' : W.toValuationSubring) : F') < M) :
    W.ord ((qO.eval x : W.toValuationSubring) : F') = W.ord ((qO.eval z' : W.toValuationSubring) : F') ∧
      ((qO.eval x : W.toValuationSubring) : F') ≠ 0 := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := qO.eval z') (fun h => h0 (by rw [h]; rfl)) hπ
  have hordz : W.ord ((qO.eval z' : W.toValuationSubring) : F') = n := by
    rw [hu]; push_cast; rw [mul_comm]
    exact W.vb_ord_irreducible_pow_mul_unit hπ n u.isUnit
  rw [hordz] at hlt ⊢
  have hnM : n + 1 ≤ M := by exact_mod_cast hlt
  obtain ⟨rr, hrr⟩ : π ^ (n + 1) ∣ qO.eval z' - qO.eval x :=
    ((pow_dvd_pow π hnM).trans hdiv).trans (Polynomial.sub_dvd_eval_sub _ _ _)
  have hqx : qO.eval x = π ^ n * (u - π * rr) := by
    have : qO.eval x = qO.eval z' - π ^ (n + 1) * rr := by rw [← hrr]; ring
    rw [this, hu]; ring
  have hunit : IsUnit ((u : W.toValuationSubring) - π * rr) := by
    refine isUnit_of_sub_mem u.isUnit ?_
    rw [show (u : W.toValuationSubring) - π * rr - u = π * (-rr) by ring, hπ.maximalIdeal_eq,
      Ideal.mem_span_singleton]
    exact Dvd.intro _ rfl
  refine ⟨?_, ?_⟩
  · rw [hqx, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    exact W.vb_ord_irreducible_pow_mul_unit hπ n hunit
  · rw [hqx, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    · intro h0
      exact hunit.ne_zero (Subtype.ext h0)

end Approx

section Generation

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  (φ : F →ₐ[K] F')

theorem adjoin_along_eq_top' (z : F')
    (hgen : IntermediateField.adjoin K (Set.range φ ∪ {z}) = ⊤) :
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    IntermediateField.adjoin F ({z} : Set F') = ⊤ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  have hle : IntermediateField.adjoin K (Set.range φ ∪ {z}) ≤
      (IntermediateField.adjoin F ({z} : Set F')).restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨a, rfl⟩ | rfl)
    · exact (IntermediateField.mem_restrictScalars _).mpr (IntermediateField.algebraMap_mem _ a)
    · exact (IntermediateField.mem_restrictScalars _).mpr
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  rw [hgen] at hle
  rw [eq_top_iff]
  intro f _
  exact (IntermediateField.mem_restrictScalars _).mp (hle IntermediateField.mem_top)

theorem exists_eval_map_eq (z : F')
    (hgen : IntermediateField.adjoin K (Set.range φ ∪ {z}) = ⊤)
    (m : Polynomial F) (hm : m.Monic) (hroot : (m.map φ.toRingHom).eval z = 0) (h : F') :
    ∃ p : Polynomial F, (p.map φ.toRingHom).eval z = h := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  have htop := adjoin_along_eq_top' φ z hgen
  have hint : IsIntegral F z := by
    refine ⟨m, hm, ?_⟩
    rw [← Polynomial.eval_map]
    exact hroot
  have hmem : h ∈ (IntermediateField.adjoin F ({z} : Set F')).toSubalgebra := by
    rw [htop]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, ?_⟩
  rw [← hp]
  show _ = Polynomial.aeval z p
  rw [Polynomial.aeval_def, Polynomial.eval_map]
  rfl

theorem exists_common_denom (W : Place K F') (T : Finset F) :
    ∃ d : F, d ≠ 0 ∧ φ d ∈ W.toValuationSubring ∧ ∀ t ∈ T, φ (d * t) ∈ W.toValuationSubring := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by rw [map_one]; exact one_mem _, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  | insert t T htT ih =>
    obtain ⟨d, hd0, hd, hT⟩ := ih
    by_cases ht : φ (d * t) ∈ W.toValuationSubring
    · refine ⟨d, hd0, hd, fun s hs => ?_⟩
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ht
      · exact hT s hs
    · have ht0 : d * t ≠ 0 := by
        intro h0; apply ht; rw [h0, map_zero]; exact zero_mem _
      have hinv : φ (d * t)⁻¹ ∈ W.toValuationSubring := by
        rcases W.toValuationSubring.mem_or_inv_mem (φ (d * t)) with h1 | h1
        · exact absurd h1 ht
        · rwa [← map_inv₀] at h1
      refine ⟨d * (d * t)⁻¹, mul_ne_zero hd0 (inv_ne_zero ht0), ?_, fun s hs => ?_⟩
      · rw [map_mul]; exact mul_mem hd hinv
      rcases Finset.mem_insert.mp hs with rfl | hs
      · have hs0 : s ≠ 0 := right_ne_zero_of_mul ht0
        have : d * (d * s)⁻¹ * s = 1 := by field_simp
        rw [this, map_one]; exact one_mem _
      · have : d * (d * t)⁻¹ * s = (d * s) * (d * t)⁻¹ := by ring
        rw [this, map_mul]; exact mul_mem (hT s hs) hinv

theorem exists_integral_repr (W : Place K F') (z : F')
    (hgen : IntermediateField.adjoin K (Set.range φ ∪ {z}) = ⊤)
    (m : Polynomial F) (hm : m.Monic) (hroot : (m.map φ.toRingHom).eval z = 0) (h : F') :
    ∃ (qq : Polynomial F) (d : F), d ≠ 0 ∧ φ d ∈ W.toValuationSubring ∧
      (∀ i : ℕ, φ (qq.coeff i) ∈ W.toValuationSubring) ∧
      (qq.map φ.toRingHom).eval z = φ d * h := by
  classical
  obtain ⟨p, hp⟩ := exists_eval_map_eq φ z hgen m hm hroot h
  obtain ⟨d, hd0, hd, hdT⟩ := exists_common_denom φ W ((Finset.range (p.natDegree + 1)).image p.coeff)
  refine ⟨Polynomial.C d * p, d, hd0, hd, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_C_mul]
    by_cases hi : i ≤ p.natDegree
    · exact hdT _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, map_zero]
      exact zero_mem _
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C, hp]
    rfl

theorem exists_lift_of_coeff_mem (W : Place K F') (qq : Polynomial F)
    (hq : ∀ i : ℕ, φ (qq.coeff i) ∈ W.toValuationSubring) :
    ∃ qO : Polynomial W.toValuationSubring, qO.map W.toValuationSubring.subtype = qq.map φ.toRingHom := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_map]
  exact ⟨⟨φ (qq.coeff n), hq n⟩, rfl⟩

variable {φ}

theorem NewtonData.ramificationIndexAlong_eq_one {W : Place K F'} {m : Polynomial F} {z : F'}
    (h : NewtonData φ W m z) (hφ : φ.toRingHom.IsIntegral)
    (hgen : IntermediateField.adjoin K (Set.range φ ∪ {z}) = ⊤) (hm : m.Monic)
    {c₀ : F} (hc₀ : φ c₀ ∈ W.toValuationSubring)
    (hdiv₀ : ∀ π : W.toValuationSubring, Irreducible π →
      π ∣ (⟨z, h.z_mem⟩ - ⟨φ c₀, hc₀⟩ : W.toValuationSubring)) :
    Place.ramificationIndexAlong φ W = 1 := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring

  obtain ⟨qq, d, hd0, hd, hqcoeff, hq⟩ := exists_integral_repr φ W z hgen m hm h.root (π : F')
  obtain ⟨qO, hqO⟩ := exists_lift_of_coeff_mem φ W qq hqcoeff
  set z' : W.toValuationSubring := ⟨z, h.z_mem⟩ with hz'
  set dO : W.toValuationSubring := ⟨φ d, hd⟩ with hdO
  have hqz : qO.eval z' = π * dO := by
    apply Subtype.ext
    rw [eval_map_coe, hqO, hq]
    push_cast
    ring
  have hd0' : (dO : F') ≠ 0 := by
    rw [hdO]; exact (map_ne_zero φ).mpr hd0
  obtain ⟨t, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := dO) (fun h0 => hd0' (by rw [h0]; rfl)) hπ
  have hordd : W.ord (φ d) = t := by
    have : (φ d) = ((dO : W.toValuationSubring) : F') := rfl
    rw [this, hu]; push_cast; rw [mul_comm]
    exact W.vb_ord_irreducible_pow_mul_unit hπ t u.isUnit
  have hordqz : W.ord ((qO.eval z' : W.toValuationSubring) : F') = (t + 1 : ℕ) := by
    rw [hqz, hu, show π * ((u : W.toValuationSubring) * π ^ t) = π ^ (t + 1) * u by ring]
    push_cast
    exact W.vb_ord_irreducible_pow_mul_unit hπ (t + 1) u.isUnit
  have hqz0 : ((qO.eval z' : W.toValuationSubring) : F') ≠ 0 := by
    rw [hqz]; push_cast
    exact mul_ne_zero (by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero) hd0'

  obtain ⟨hc, hdiv⟩ := h.seq hπ hc₀ (hdiv₀ π hπ) (t + 2)
  set x : W.toValuationSubring := ⟨φ (newtonSeq m c₀ (t + 2)), hc⟩ with hx
  have hdiv' : π ^ (t + 2) ∣ z' - x :=
    (pow_dvd_pow π (Nat.lt_two_pow_self).le).trans hdiv
  obtain ⟨hordx, hx0⟩ := ord_eval_eq_of_pow_dvd W hπ qO hdiv' hqz0 (by rw [hordqz]; push_cast; omega)
  rw [hordqz] at hordx

  set f : F := qq.eval (newtonSeq m c₀ (t + 2)) / d with hf
  have hφq : φ (qq.eval (newtonSeq m c₀ (t + 2))) = ((qO.eval x : W.toValuationSubring) : F') := by
    rw [eval_map_coe, hqO, hx]
    exact (eval_map_apply qq _).symm
  have hq0 : φ (qq.eval (newtonSeq m c₀ (t + 2))) ≠ 0 := by rw [hφq]; exact hx0
  have hordf : W.ord (φ f) = 1 := by
    rw [hf, map_div₀, div_eq_mul_inv, W.ord_mul hq0 (inv_ne_zero ((map_ne_zero φ).mpr hd0)),
      W.ord_inv, hφq, hordx, hordd]
    push_cast
    ring
  have hf0 : f ≠ 0 := by
    intro h0
    have : W.ord (φ f) = 0 := by rw [h0, map_zero, Place.ord_zero]
    omega

  have hle := W.ramificationIndex_le_ord (F := F) hf0 (by
    show 0 < W.ord (φ f)
    omega)
  have hpos := W.ramificationIndex_pos (F := F)
  show W.ramificationIndex F = 1
  have hle' : (W.ramificationIndex F : ℤ) ≤ 1 := by
    have : W.ord (algebraMap F F' f) = W.ord (φ f) := rfl
    omega
  omega

end Generation

end VbUnrq

namespace VbUnrq

section ValuesGeneric

variable {K F' : Type*} [Field K] [Field F'] [Algebra K F'] (W : Place K F')

theorem hasValue_iff_sub_mem {g : F'} (hg : g ∈ W.toValuationSubring) (b : K) :
    W.HasValue g b ↔ (⟨g - algebraMap K F' b, sub_mem hg (W.algebraMap_mem' b)⟩ : W.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal W.toValuationSubring := by
  rw [← W.vb_hasValue_zero_iff_mem_maximalIdeal]
  constructor
  · intro h
    have := W.vb_hasValue_add h (W.vb_hasValue_neg (W.hasValue_algebraMap b))
    rwa [add_neg_cancel, ← sub_eq_add_neg] at this
  · intro h
    have := W.vb_hasValue_add h (W.hasValue_algebraMap b)
    rwa [zero_add, sub_add_cancel] at this

theorem hasValue_pow {g : F'} {a : K} (h : W.HasValue g a) (n : ℕ) : W.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact W.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem hasValue_sum {ι : Type*} (s : Finset ι) (g : ι → F') (a : ι → K)
    (h : ∀ i ∈ s, W.HasValue (g i) (a i)) : W.HasValue (∑ i ∈ s, g i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact W.vb_hasValue_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact W.vb_hasValue_add (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasValue_eval (p : Polynomial F') {n : ℕ} (hn : p.natDegree < n) (β : ℕ → K)
    (hβ : ∀ i, W.HasValue (p.coeff i) (β i)) {z : F'} {a : K} (hz : W.HasValue z a) :
    W.HasValue (p.eval z) (∑ i ∈ Finset.range n, β i * a ^ i) := by
  rw [Polynomial.eval_eq_sum_range' hn]
  exact hasValue_sum W _ _ _ fun i _ => (hβ i).mul (hasValue_pow W hz i)

theorem isUnit_iff_ord_eq_zero {g : F'} (hg : g ∈ W.toValuationSubring) (hg0 : g ≠ 0) :
    IsUnit (⟨g, hg⟩ : W.toValuationSubring) ↔ W.ord g = 0 := by
  constructor
  · intro hu
    have := W.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := W.exists_isUnit_of_ord_eq_zero hg0 h0
    exact hu

end ValuesGeneric

section AlongValues

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

theorem restrictAlong_mem_iff (W : Place K F') (f : F) :
    f ∈ (W.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ W.toValuationSubring := Iff.rfl

theorem mem_iff_mem_of_restrictAlong_eq {W W' : Place K F'}
    (hres : W'.restrictAlong φ hφ = W.restrictAlong φ hφ) (f : F) :
    φ f ∈ W'.toValuationSubring ↔ φ f ∈ W.toValuationSubring := by
  rw [← restrictAlong_mem_iff φ hφ W' f, ← restrictAlong_mem_iff φ hφ W f, hres]

theorem ord_eq_ord_of_restrictAlong_eq {W W' : Place K F'}
    (hres : W'.restrictAlong φ hφ = W.restrictAlong φ hφ)
    (he : Place.ramificationIndexAlong φ W = 1) (he' : Place.ramificationIndexAlong φ W' = 1) (f : F) :
    W'.ord (φ f) = W.ord (φ f) := by
  have h1 := Place.ord_restrictAlong φ hφ W f
  have h2 := Place.ord_restrictAlong φ hφ W' f
  rw [he] at h1; rw [he', hres] at h2
  push_cast at h1 h2
  rw [h1, h2]

theorem hasValue_of_restrictAlong_eq {W W' : Place K F'}
    (hres : W'.restrictAlong φ hφ = W.restrictAlong φ hφ) {f : F} {b : K}
    (h : W.HasValue (φ f) b) : W'.HasValue (φ f) b := by
  have hmem : φ f ∈ W.toValuationSubring := h.mem
  have hmem' : φ f ∈ W'.toValuationSubring := (mem_iff_mem_of_restrictAlong_eq φ hφ hres f).mpr hmem
  rw [hasValue_iff_sub_mem W hmem] at h
  rw [hasValue_iff_sub_mem W' hmem']

  have hφ' : φ f - algebraMap K F' b = φ (f - algebraMap K F b) := by
    rw [map_sub, AlgHom.commutes]
  by_cases h0 : φ f - algebraMap K F' b = 0
  · have : (⟨φ f - algebraMap K F' b, sub_mem hmem' (W'.algebraMap_mem' b)⟩ : W'.toValuationSubring) = 0 :=
      Subtype.ext h0
    rw [this]; exact zero_mem _

  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  rw [isUnit_iff_ord_eq_zero W' _ h0]
  rw [isUnit_iff_ord_eq_zero W _ h0] at h
  intro h1; apply h

  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have e1 := Place.ord_restrictAlong φ hφ W (f - algebraMap K F b)
  have e2 := Place.ord_restrictAlong φ hφ W' (f - algebraMap K F b)
  rw [hres] at e2
  rw [← hφ'] at e1 e2
  rw [h1] at e2
  have hp : 0 < Place.ramificationIndexAlong φ W' := by
    show 0 < W'.ramificationIndex F
    exact W'.ramificationIndex_pos (F := F)
  have hu : (W.restrictAlong φ hφ).ord (f - algebraMap K F b) = 0 := by
    rcases mul_eq_zero.mp e2.symm with h3 | h3
    · exfalso; exact (ne_of_gt hp) (by exact_mod_cast h3)
    · exact h3
  rw [e1, hu, mul_zero]

end AlongValues

end VbUnrq

namespace VbUnrq

section Final

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
  {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}

local notation "Lb" => AlgebraicClosure ℚ

theorem newtonData_of_chart (hS : IsChartAt R v S)
    {W : Place Lb (modularFunctionFieldBar (N * q))} (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v)
    {z : modularFunctionFieldBar (N * q)} {m : Polynomial (modularFunctionFieldBar N)} (hzS : z ∈ S)
    (hmz : (m.map (heckeAlphaBar Lb N q).toRingHom).eval z = 0)
    (hmcoeff : ∀ i : ℕ, heckeAlphaBar Lb N q (m.coeff i) ∈ Subring.closure S)
    (hdiff : ∀ h : (Polynomial.derivative (m.map (heckeAlphaBar Lb N q).toRingHom)).eval z ∈ R.R₁.integers,
      ¬ v.HasValue (R.residue₁ ⟨_, h⟩) (0 : k)) :
    NewtonData (heckeAlphaBar Lb N q) W m z where
  z_mem := hS.regularOver z hzS W hWv
  coeff_mem i := closure_le_place hS hWv _ (hmcoeff i)
  root := hmz
  unit := by
    obtain ⟨a, hau, ha⟩ := exists_hasValue_ne_zero_of_etale hS hW hWv
      (eval_derivative_map_mem_closure z (Subring.subset_closure hzS) m hmcoeff) hdiff
    refine ⟨(a : Lb), fun h0 => hau.ne_zero ?_, ha⟩
    exact_mod_cast h0

theorem first_approx {W : Place Lb (modularFunctionFieldBar (N * q))}
    {z : modularFunctionFieldBar (N * q)} {m : Polynomial (modularFunctionFieldBar N)}
    (hND : NewtonData (heckeAlphaBar Lb N q) W m z) {a : A} (hza : W.HasValue z (a : Lb)) :
    ∃ hc : heckeAlphaBar Lb N q (algebraMap Lb (modularFunctionFieldBar N) (a : Lb)) ∈ W.toValuationSubring,
      ∀ π : W.toValuationSubring, Irreducible π →
        π ∣ (⟨z, hND.z_mem⟩ - ⟨heckeAlphaBar Lb N q (algebraMap Lb (modularFunctionFieldBar N) (a : Lb)), hc⟩ :
          W.toValuationSubring) := by
  have hφc : heckeAlphaBar Lb N q (algebraMap Lb (modularFunctionFieldBar N) (a : Lb)) =
      algebraMap Lb (modularFunctionFieldBar (N * q)) (a : Lb) := AlgHom.commutes _ _
  refine ⟨by rw [hφc]; exact W.algebraMap_mem' _, fun π hπ => ?_⟩
  have hm := (hasValue_iff_sub_mem W hND.z_mem (a : Lb)).mp hza
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  convert hm using 1
  exact Subtype.ext (by simp only [hφc]; rfl)

theorem ramificationIndexAlong_eq_one_of_chart (hS : IsChartAt R v S)
    {W : Place Lb (modularFunctionFieldBar (N * q))} (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v) :
    Place.ramificationIndexAlong (heckeAlphaBar Lb N q) W = 1 := by
  obtain ⟨z, m, hzS, -, hadj, hmonic, -, hmz, hmcoeff, hdiff⟩ := hS.etale
  have hND := newtonData_of_chart hS hW hWv hzS hmz hmcoeff hdiff
  obtain ⟨a, ha, -⟩ := hS.valueLaw z hzS W hW hWv
  obtain ⟨hc, hdv⟩ := first_approx hND ha
  exact hND.ramificationIndexAlong_eq_one hα hadj hmonic hc hdv

theorem coeff_sum_C_mul_X_pow {T : Type*} [CommRing T] (b : ℕ → T) (n j : ℕ) :
    (∑ i ∈ Finset.range n, Polynomial.C (b i) * Polynomial.X ^ i).coeff j = if j < n then b j else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range n) j b]
  simp [Finset.mem_range]

set_option maxHeartbeats 8000000 in

theorem eq_of_isStrictFst_of_restrictAlong_eq (hS : IsChartAt R v S)
    {W W' : Place Lb (modularFunctionFieldBar (N * q))} (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v)
    (hW' : P.IsStrictFst W')
    (hres : W'.restrictAlong (heckeAlphaBar Lb N q) hα = W.restrictAlong (heckeAlphaBar Lb N q) hα) :
    W' = W := by
  classical
  have hW'v : P.reduceFst W' = v := by
    show P.sp (W'.restrictAlong (heckeAlphaBar Lb N q) hα) = v
    rw [hres]; exact hWv
  obtain ⟨z, m, hzS, -, hadj, hmonic, hdeg, hmz, hmcoeff, hdiff⟩ := hS.etale
  have hND := newtonData_of_chart hS hW hWv hzS hmz hmcoeff hdiff
  have hND' := newtonData_of_chart hS hW' hW'v hzS hmz hmcoeff hdiff
  obtain ⟨a, ha, hav⟩ := hS.valueLaw z hzS W hW hWv
  obtain ⟨a', ha', hav'⟩ := hS.valueLaw z hzS W' hW' hW'v
  set φ := heckeAlphaBar Lb N q with hφdef
  by_cases haa : a = a'
  ·
    subst haa
    obtain ⟨hc, hdv⟩ := first_approx hND ha
    obtain ⟨hc', hdv'⟩ := first_approx hND' ha'
    have he := hND.ramificationIndexAlong_eq_one hα hadj hmonic hc hdv
    have he' := hND'.ramificationIndexAlong_eq_one hα hadj hmonic hc' hdv'
    set c₀ : modularFunctionFieldBar N := algebraMap Lb (modularFunctionFieldBar N) (a : Lb) with hc₀

    have hord : ∀ hh : modularFunctionFieldBar (N * q), hh ≠ 0 → W'.ord hh = W.ord hh := by
      intro hh hh0
      obtain ⟨qq, d, hd0, hd, hqcoeff, hq⟩ := exists_integral_repr φ W z hadj m hmonic hmz hh
      have hqcoeff' : ∀ i, φ (qq.coeff i) ∈ W'.toValuationSubring := fun i =>
        (mem_iff_mem_of_restrictAlong_eq φ hα hres _).mpr (hqcoeff i)
      obtain ⟨qO, hqO⟩ := exists_lift_of_coeff_mem φ W qq hqcoeff
      obtain ⟨qO', hqO'⟩ := exists_lift_of_coeff_mem φ W' qq hqcoeff'
      have hH0 : φ d * hh ≠ 0 := mul_ne_zero ((_root_.map_ne_zero φ).mpr hd0) hh0
      have hz1 : ((qO.eval ⟨z, hND.z_mem⟩ : W.toValuationSubring) : modularFunctionFieldBar (N * q)) = φ d * hh := by
        rw [eval_map_coe, hqO, hq]
      have hz2 : ((qO'.eval ⟨z, hND'.z_mem⟩ : W'.toValuationSubring) : modularFunctionFieldBar (N * q)) = φ d * hh := by
        rw [eval_map_coe, hqO', hq]
      obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, W.ord (φ d * hh) < M ∧ W'.ord (φ d * hh) < M :=
        ⟨(max (W.ord (φ d * hh)) (W'.ord (φ d * hh))).toNat + 1, by omega, by omega⟩
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
      obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible W'.toValuationSubring
      obtain ⟨hcM, hdivM⟩ := hND.seq hπ hc (hdv π hπ) M
      obtain ⟨hcM', hdivM'⟩ := hND'.seq hπ' hc' (hdv' π' hπ') M
      have hle : M ≤ 2 ^ M := (Nat.lt_two_pow_self).le
      obtain ⟨h1, -⟩ := ord_eval_eq_of_pow_dvd W hπ qO ((pow_dvd_pow π hle).trans hdivM)
        (by rw [hz1]; exact hH0) (by rw [hz1]; exact hM1)
      obtain ⟨h2, -⟩ := ord_eval_eq_of_pow_dvd W' hπ' qO' ((pow_dvd_pow π' hle).trans hdivM')
        (by rw [hz2]; exact hH0) (by rw [hz2]; exact hM2)
      rw [hz1] at h1
      rw [hz2] at h2
      have hg1 : ((qO.eval ⟨φ (newtonSeq m c₀ M), hcM⟩ : W.toValuationSubring) : modularFunctionFieldBar (N * q)) =
          φ (qq.eval (newtonSeq m c₀ M)) := by
        rw [eval_map_coe, hqO]; exact eval_map_apply qq _
      have hg2 : ((qO'.eval ⟨φ (newtonSeq m c₀ M), hcM'⟩ : W'.toValuationSubring) : modularFunctionFieldBar (N * q)) =
          φ (qq.eval (newtonSeq m c₀ M)) := by
        rw [eval_map_coe, hqO']; exact eval_map_apply qq _
      rw [hg1] at h1
      rw [hg2] at h2
      have hgg := ord_eq_ord_of_restrictAlong_eq φ hα hres he he' (qq.eval (newtonSeq m c₀ M))
      have hdd := ord_eq_ord_of_restrictAlong_eq φ hα hres he he' d
      have hH : W'.ord (φ d * hh) = W.ord (φ d * hh) := by rw [← h1, ← h2, hgg]
      rw [W.ord_mul ((_root_.map_ne_zero φ).mpr hd0) hh0, W'.ord_mul ((_root_.map_ne_zero φ).mpr hd0) hh0, hdd] at hH
      omega

    apply Place.ext
    ext x
    by_cases hx : x = 0
    · subst hx; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    rw [W'.mem_iff_ord_nonneg hx, W.mem_iff_ord_nonneg hx, hord x hx]
  ·
    exfalso
    have hred : red a = red a' := hav.unique hav'

    have hb0 : ∀ i, ∃ b : A, W.HasValue (φ (m.coeff i)) (b : Lb) := fun i => by
      obtain ⟨b, hb, -⟩ := valueLaw_closure hS hW hWv (hmcoeff i); exact ⟨b, hb⟩
    choose b hb using hb0
    have hb' : ∀ i, W'.HasValue (φ (m.coeff i)) (b i : Lb) := fun i =>
      hasValue_of_restrictAlong_eq φ hα hres (hb i)
    set n := m.natDegree + 1 with hn
    have hdegmap : (m.map φ.toRingHom).natDegree < n :=
      lt_of_le_of_lt Polynomial.natDegree_map_le (by omega)

    have hsum : ∀ {V : Place Lb (modularFunctionFieldBar (N * q))} {x : A},
        (∀ i, V.HasValue (φ (m.coeff i)) (b i : Lb)) → V.HasValue z (x : Lb) →
        ∑ i ∈ Finset.range n, (b i : Lb) * (x : Lb) ^ i = 0 := by
      intro V x hbV hzx
      have h1 := hasValue_eval V (m.map φ.toRingHom) hdegmap (fun i => (b i : Lb))
        (fun i => by rw [Polynomial.coeff_map]; exact hbV i) hzx
      rw [hmz] at h1
      exact (V.vb_hasValue_zero.unique h1).symm
    have hra := hsum hb ha
    have hra' := hsum hb' ha'

    have hdegd : (Polynomial.derivative (m.map φ.toRingHom)).natDegree < m.natDegree := by
      have h1 := Polynomial.natDegree_derivative_le (m.map φ.toRingHom)
      have h2 : (m.map φ.toRingHom).natDegree ≤ m.natDegree := Polynomial.natDegree_map_le
      omega
    have hderiv := hasValue_eval W (Polynomial.derivative (m.map φ.toRingHom)) hdegd
      (fun i => (b (i + 1) : Lb) * ((i : Lb) + 1)) (fun i => by
        rw [Polynomial.coeff_derivative, Polynomial.coeff_map]
        have hc := W.hasValue_algebraMap ((i : Lb) + 1)
        rw [map_add, map_natCast, map_one] at hc
        exact (hb (i + 1)).mul hc) ha
    obtain ⟨a₀, ha₀u, ha₀⟩ := exists_hasValue_ne_zero_of_etale hS hW hWv
      (eval_derivative_map_mem_closure z (Subring.subset_closure hzS) m hmcoeff) hdiff
    have ha₀eq := ha₀.unique hderiv

    set mbar : Polynomial A := ∑ i ∈ Finset.range n, Polynomial.C (b i) * Polynomial.X ^ i with hmbar
    have hcoeff : ∀ j, mbar.coeff j = if j < n then b j else 0 := coeff_sum_C_mul_X_pow b n
    have hevalA : ∀ x : A, ((mbar.eval x : A) : Lb) = ∑ i ∈ Finset.range n, (b i : Lb) * (x : Lb) ^ i := by
      intro x
      rw [hmbar, Polynomial.eval_finsetSum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast; ring
    have hrootA : mbar.IsRoot a := by
      have := hevalA a; rw [hra] at this
      exact_mod_cast this
    have hrootA' : mbar.IsRoot a' := by
      have := hevalA a'; rw [hra'] at this
      exact_mod_cast this
    have hderivA : (((Polynomial.derivative mbar).eval a : A) : Lb) =
        ∑ i ∈ Finset.range m.natDegree, (b (i + 1) : Lb) * ((i : Lb) + 1) * (a : Lb) ^ i := by
      rw [hmbar, Polynomial.derivative_sum]
      simp only [Polynomial.derivative_C_mul_X_pow]
      rw [Polynomial.eval_finsetSum, hn, Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, Polynomial.C_0, zero_mul, Polynomial.eval_zero, add_zero,
        Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have ha₀A : a₀ = (Polynomial.derivative mbar).eval a := by
      apply Subtype.ext
      rw [hderivA]
      exact ha₀eq
    have hunitD : IsUnit ((Polynomial.derivative mbar).eval a) := ha₀A ▸ ha₀u

    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial A, (Polynomial.X - Polynomial.C a) * Q = mbar :=
      ⟨mbar /ₘ (Polynomial.X - Polynomial.C a), (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hrootA⟩
    have hQa' : Q.IsRoot a' := by
      have h1 := congrArg (Polynomial.eval a') hQ
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hrootA'.eq_zero] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (sub_eq_zero.mp h2) (Ne.symm haa)
      · exact h2
    obtain ⟨R', hR'⟩ : ∃ R' : Polynomial A, (Polynomial.X - Polynomial.C a') * R' = Q :=
      ⟨Q /ₘ (Polynomial.X - Polynomial.C a'), (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hQa'⟩
    have hder : (Polynomial.derivative mbar).eval a = (a - a') * R'.eval a := by
      rw [← hQ, Polynomial.derivative_mul]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
        one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, zero_mul, add_zero]
      rw [← hR']
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hmem : a - a' ∈ IsLocalRing.maximalIdeal A :=
      mem_maximalIdeal_of_red_eq_zero red (by rw [map_sub, hred, sub_self])
    have hmem' : (Polynomial.derivative mbar).eval a ∈ IsLocalRing.maximalIdeal A := by
      rw [hder]; exact Ideal.mul_mem_right _ _ hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem' hunitD

end Final

end VbUnrq

open VbUnrq in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}
    (hqN : ¬ q ∣ N) (hS : IsChartAt R v S)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v) :
    Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) W = 1 ∧
    ∀ W' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst W' →
      W'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα =
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα → W' = W :=
  ⟨ramificationIndexAlong_eq_one_of_chart hS hW hWv,
   fun W' hW' hres => eq_of_isStrictFst_of_restrictAlong_eq hS hW hWv hW' hres⟩

end S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst (solution)
