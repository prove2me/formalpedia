-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.count_differentIdeal_eq_finsum_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T07:22:39.893952+00:00
-- url     : https://prove2.me/submissions/7936a997-f5dd-463e-8741-ee9a73e796ad

import Mathlib

set_option autoImplicit false

noncomputable section

section Inline_Swan_Herb


/-!
# S4-Swan (K2), part 1: ramification functions, lower and upper numbering, the Herbrand function

A *ramification function* on a group `G` (the inertia group of a totally ramified finite Galois extension of
discretely valued fields, so `G = G_0`) is `i : G → ℕ∞` with `i σ = ⊤ ↔ σ = 1`, `1 ≤ i σ`, the ultrametric
inequality `min (i σ) (i τ) ≤ i (σ τ)`, and invariance under inversion and conjugation (Serre, *Local Fields*
IV §1: `i_G(σ) = v_L(σ x - x)` for a generator `x` of the valuation ring).

* lower numbering `G_u = {σ | u + 1 ≤ i σ}` (`lower`), normal subgroups, `G_0 = G`;
* the Herbrand function, defined by Serre's sum formula (IV §3)
  `φ(m) = (1/|G|) ∑_σ min (i σ, m + 1) - 1` on `ℕ`; `φ(m+1) = φ(m) + |G_{m+1}|/|G|`, strictly monotone, unbounded;
* upper numbering `G^v = G_{ψ(v)}` with `ψ(v) = min {m | v ≤ φ m}` (`upper`), and
  `σ ∈ G^v ↔ v ≤ φ(i σ - 1)` for `σ ≠ 1` (`mem_upper`).
-/


namespace RamanujanPetersson
namespace Swan

noncomputable section

/-- A ramification function on a group (the totally ramified case `G = G_0`). -/
structure RamFn (G : Type*) [Group G] where
  /-- `i σ = v_L(σ π - π)`. -/
  i : G → ℕ∞
  i_eq_top : ∀ σ, i σ = ⊤ ↔ σ = 1
  one_le : ∀ σ, 1 ≤ i σ
  le_mul : ∀ σ τ, min (i σ) (i τ) ≤ i (σ * τ)
  i_inv : ∀ σ, i σ⁻¹ = i σ
  i_conj : ∀ σ τ, i (τ * σ * τ⁻¹) = i σ

namespace RamFn

variable {G : Type*} [Group G] (R : RamFn G)

theorem i_one : R.i 1 = ⊤ := (R.i_eq_top 1).2 rfl

theorem i_ne_top {σ : G} (h : σ ≠ 1) : R.i σ ≠ ⊤ := fun h' => h ((R.i_eq_top σ).1 h')

theorem exists_i_eq {σ : G} (h : σ ≠ 1) : ∃ n : ℕ, 1 ≤ n ∧ R.i σ = n := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (R.i_ne_top h)
  refine ⟨n, ?_, hn.symm⟩
  have h1 := R.one_le σ
  rw [← hn] at h1
  exact_mod_cast h1

/-- Ultrametric equality: `i (σ τ) = i τ` when `i τ < i σ`. -/
theorem i_mul_of_lt {σ τ : G} (h : R.i τ < R.i σ) : R.i (σ * τ) = R.i τ := by
  apply le_antisymm
  · have h1 := R.le_mul σ⁻¹ (σ * τ)
    rw [R.i_inv, inv_mul_cancel_left] at h1
    by_contra hc
    exact absurd h1 (not_le.2 (lt_min h (not_le.1 hc)))
  · calc R.i τ = min (R.i σ) (R.i τ) := (min_eq_right h.le).symm
      _ ≤ _ := R.le_mul σ τ

/-- If `σ` has maximal `i` on `σ τ`, then `i (σ τ) = min (i τ) (i σ)` (Serre IV §3, proof of Lemma 5). -/
theorem i_mul_eq_min {σ τ : G} (hmax : R.i (σ * τ) ≤ R.i σ) :
    R.i (σ * τ) = min (R.i τ) (R.i σ) := by
  rcases lt_or_ge (R.i τ) (R.i σ) with h | h
  · rw [R.i_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    exact le_antisymm hmax (le_trans (le_min le_rfl h) (R.le_mul σ τ))

/-- Lower numbering ramification groups `G_u = {σ | u + 1 ≤ i σ}`. -/
def lower (u : ℕ) : Subgroup G where
  carrier := {σ | ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ}
  one_mem' := by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i 1
    rw [R.i_one]; exact le_top
  mul_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (R.le_mul a b)
  inv_mem' := fun {a} ha => by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i a⁻¹
    rw [R.i_inv]; exact ha

theorem mem_lower {u : ℕ} {σ : G} : σ ∈ R.lower u ↔ ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ := Iff.rfl

instance lower_normal (u : ℕ) : (R.lower u).Normal where
  conj_mem := fun σ hσ τ => by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i (τ * σ * τ⁻¹)
    rw [R.i_conj]; exact hσ

theorem lower_zero : R.lower 0 = ⊤ := by
  ext σ
  simp only [Subgroup.mem_top, iff_true, mem_lower, zero_add, Nat.cast_one]
  exact R.one_le σ

theorem lower_antitone : Antitone R.lower := fun u v h σ hσ => by
  show ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ
  exact le_trans (Nat.cast_le.2 (Nat.succ_le_succ h)) hσ

/-- The lower index `j σ = i σ - 1` (`σ ∈ G_u ↔ u ≤ j σ` for `σ ≠ 1`). -/
def jdx (σ : G) : ℕ := (R.i σ).toNat - 1

theorem mem_lower_iff {σ : G} (h : σ ≠ 1) (u : ℕ) : σ ∈ R.lower u ↔ u ≤ R.jdx σ := by
  obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h
  rw [mem_lower, jdx, hn, ENat.toNat_coe, Nat.cast_le]
  omega

/-- The restriction of a ramification function to a subgroup. -/
def restrict (H : Subgroup G) : RamFn H where
  i := fun τ => R.i τ
  i_eq_top := fun τ => by
    rw [R.i_eq_top]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  one_le := fun τ => R.one_le τ
  le_mul := fun σ τ => R.le_mul σ τ
  i_inv := fun τ => R.i_inv τ
  i_conj := fun σ τ => R.i_conj σ τ

theorem restrict_i (H : Subgroup G) (τ : H) : (R.restrict H).i τ = R.i τ := rfl

/-! ## The Herbrand function -/

variable [Fintype G]

/-- `w σ m = min (i σ) (m + 1)` as a natural number. -/
def w (σ : G) (m : ℕ) : ℕ := (min (R.i σ) ((m + 1 : ℕ) : ℕ∞)).toNat

theorem w_one (m : ℕ) : R.w 1 m = m + 1 := by
  rw [w, R.i_one, min_eq_right le_top, ENat.toNat_coe]

theorem w_of_eq {σ : G} {n : ℕ} (h : R.i σ = n) (m : ℕ) : R.w σ m = min n (m + 1) := by
  rw [w, h]
  rcases le_total n (m + 1) with hh | hh
  · rw [min_eq_left (Nat.cast_le.2 hh), min_eq_left hh, ENat.toNat_coe]
  · rw [min_eq_right (Nat.cast_le.2 hh), min_eq_right hh, ENat.toNat_coe]

theorem w_zero (σ : G) : R.w σ 0 = 1 := by
  by_cases h : σ = 1
  · rw [h, R.w_one]
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h
    rw [R.w_of_eq hn]; omega

theorem w_succ_of_mem {σ : G} {m : ℕ} (h : σ ∈ R.lower (m + 1)) : R.w σ (m + 1) = R.w σ m + 1 := by
  by_cases h1 : σ = 1
  · rw [h1, R.w_one, R.w_one]
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h1
    rw [mem_lower, hn, Nat.cast_le] at h
    rw [R.w_of_eq hn, R.w_of_eq hn]; omega

theorem w_succ_of_not_mem {σ : G} {m : ℕ} (h : σ ∉ R.lower (m + 1)) : R.w σ (m + 1) = R.w σ m := by
  by_cases h1 : σ = 1
  · exact absurd (h1 ▸ (R.lower (m + 1)).one_mem) h
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h1
    rw [mem_lower, hn, Nat.cast_le] at h
    rw [R.w_of_eq hn, R.w_of_eq hn]; omega

/-- The Herbrand function `φ(m) = (1/|G|) ∑_σ min (i σ, m + 1) - 1` (Serre IV §3). -/
def phi (m : ℕ) : ℚ := (∑ σ : G, (R.w σ m : ℚ)) / Nat.card G - 1

theorem cardG_pos : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos

theorem phi_zero : R.phi 0 = 0 := by
  have h : (∑ σ : G, (R.w σ 0 : ℚ)) = Nat.card G := by
    simp [R.w_zero, Nat.card_eq_fintype_card]
  rw [phi, h, div_self ((cardG_pos (G := G))).ne', sub_self]

theorem phi_succ (m : ℕ) : R.phi (m + 1) = R.phi m + Nat.card (R.lower (m + 1)) / Nat.card G := by
  classical
  have h : (∑ σ : G, (R.w σ (m + 1) : ℚ)) =
      (∑ σ : G, (R.w σ m : ℚ)) + ∑ σ : G, (if σ ∈ R.lower (m + 1) then (1 : ℚ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : σ ∈ R.lower (m + 1)
    · rw [R.w_succ_of_mem hσ, if_pos hσ]; push_cast; ring
    · rw [R.w_succ_of_not_mem hσ, if_neg hσ, add_zero]
  have hc : (∑ σ : G, (if σ ∈ R.lower (m + 1) then (1 : ℚ) else 0)) = Nat.card (R.lower (m + 1)) := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [phi, phi, h, hc, add_div]; ring

theorem phi_lt_succ (m : ℕ) : R.phi m < R.phi (m + 1) := by
  rw [R.phi_succ]
  have : (0 : ℚ) < Nat.card (R.lower (m + 1)) := by exact_mod_cast Nat.card_pos
  linarith [div_pos this (cardG_pos (G := G))]

theorem phi_strictMono : StrictMono R.phi := strictMono_nat_of_lt_succ R.phi_lt_succ

theorem phi_le_iff {a b : ℕ} : R.phi a ≤ R.phi b ↔ a ≤ b := R.phi_strictMono.le_iff_le

theorem phi_ge (m : ℕ) : (m : ℚ) / Nat.card G ≤ R.phi m := by
  induction m with
  | zero => rw [R.phi_zero]; simp
  | succ m ih =>
    rw [R.phi_succ]
    have h1 : (1 : ℚ) ≤ Nat.card (R.lower (m + 1)) := by exact_mod_cast Nat.card_pos
    have h2 : (1 : ℚ) / Nat.card G ≤ Nat.card (R.lower (m + 1)) / Nat.card G :=
      div_le_div_of_nonneg_right h1 (cardG_pos (G := G)).le
    have h3 : ((m + 1 : ℕ) : ℚ) / Nat.card G = (m : ℚ) / Nat.card G + 1 / Nat.card G := by
      push_cast; ring
    linarith

/-- `φ` is the lower-numbering sum `φ(m) = ∑_{1 ≤ u ≤ m} |G_u| / |G|`. -/
theorem phi_eq_sum (m : ℕ) :
    R.phi m = ∑ u ∈ Finset.range m, (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G := by
  induction m with
  | zero => rw [R.phi_zero, Finset.sum_range_zero]
  | succ m ih => rw [R.phi_succ, ih, Finset.sum_range_succ]

theorem exists_le_phi (v : ℚ) : ∃ m : ℕ, v ≤ R.phi m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (v * Nat.card G)
  refine ⟨m, le_trans ?_ (R.phi_ge m)⟩
  rw [le_div_iff₀ (cardG_pos (G := G))]; exact hm.le

/-! ## Upper numbering -/

/-- `ψ(v) = min {m | v ≤ φ m}`. -/
def upperIdx (v : ℚ) : ℕ := Nat.find (R.exists_le_phi v)

/-- Upper numbering ramification groups `G^v = G_{ψ(v)}`. -/
def upper (v : ℚ) : Subgroup G := R.lower (R.upperIdx v)

instance upper_normal (v : ℚ) : (R.upper v).Normal := R.lower_normal _

theorem upperIdx_le_iff (v : ℚ) (n : ℕ) : R.upperIdx v ≤ n ↔ v ≤ R.phi n := by
  rw [upperIdx, Nat.find_le_iff]
  constructor
  · rintro ⟨m, hm, hv⟩; exact le_trans hv (R.phi_le_iff.2 hm)
  · intro h; exact ⟨n, le_rfl, h⟩

/-- `σ ∈ G^v ↔ v ≤ φ(i σ - 1)` for `σ ≠ 1`. -/
theorem mem_upper {σ : G} (h : σ ≠ 1) (v : ℚ) : σ ∈ R.upper v ↔ v ≤ R.phi (R.jdx σ) := by
  rw [upper, R.mem_lower_iff h, R.upperIdx_le_iff]

theorem upper_antitone : Antitone R.upper := fun v v' hv σ hσ => by
  by_cases h : σ = 1
  · rw [h]; exact Subgroup.one_mem _
  · rw [R.mem_upper h] at hσ ⊢; exact le_trans hv hσ

theorem upper_eq_top {v : ℚ} (hv : v ≤ 0) : R.upper v = ⊤ := by
  have : R.upperIdx v = 0 := by
    rw [← Nat.le_zero, R.upperIdx_le_iff, R.phi_zero]; exact hv
  rw [upper, this, R.lower_zero]

end RamFn

end

end Swan
end RamanujanPetersson

end Inline_Swan_Herb

section Inline_Swan_Loc


/-!
# S4-Swan (K2), part 6: local totally ramified data give a ramification function

`LocData G L`: a finite group `G` acting faithfully on a field `L`, a `G`-invariant discrete valuation
`v : L → ℤ ∪ {⊤}` with a uniformizer `ϖ` (`v ϖ = 1`), and the residue condition `res`: every integral `x` is
congruent mod `𝔭` to a `G`-invariant element (residue field of `L^G` = residue field of `L`, `G` acts trivially on it).
No completeness and no monogenicity are assumed: `res` gives the successive approximation that replaces
`B = A[ϖ]` (Serre, Local Fields IV §1). Then (`lb`) `v(σ ϖ_H - ϖ_H) ≤ v(σ x - x)` for every integral `H`-invariant
`x` and every element `ϖ_H` of `L^H` of minimal valuation, so `i(σ) = v(σ ϖ - ϖ)` is independent of `ϖ` and
defines a `RamFn G` (`LocData.ramFn`).
-/


namespace RamanujanPetersson
namespace Swan

noncomputable section

/-- `ℤ ∪ {⊤} → ℕ∞`, truncating negatives. -/
def toENat (w : WithTop ℤ) : ℕ∞ := WithTop.map Int.toNat w

theorem toENat_top : toENat ⊤ = ⊤ := rfl

theorem toENat_coe (m : ℤ) : toENat (m : WithTop ℤ) = (m.toNat : ℕ∞) := rfl

theorem toENat_eq_top_iff (w : WithTop ℤ) : toENat w = ⊤ ↔ w = ⊤ := WithTop.map_eq_top_iff

theorem toENat_mono : Monotone toENat := by
  intro a b h
  induction b with
  | top => rw [toENat_top]; exact le_top
  | coe b =>
    induction a with
    | top => exact absurd h (by simp)
    | coe a =>
      rw [toENat_coe, toENat_coe]
      exact_mod_cast Int.toNat_le_toNat (WithTop.coe_le_coe.1 h)

theorem eq_top_of_forall_nat_le {w : WithTop ℤ} (h : ∀ n : ℕ, (n : WithTop ℤ) ≤ w) : w = ⊤ := by
  induction w with
  | top => rfl
  | coe m =>
    exfalso
    have := h (m.toNat + 1)
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
    omega

variable (G L : Type*) [Group G] [Field L] [MulSemiringAction G L]

/-- Local totally ramified data (see the module docstring). -/
structure LocData where
  v : AddValuation L (WithTop ℤ)
  v_smul : ∀ (σ : G) (x : L), v (σ • x) = v x
  faithful : ∀ σ : G, (∀ x : L, σ • x = x) → σ = 1
  ϖ : L
  v_ϖ : v ϖ = 1
  res : ∀ x : L, 0 ≤ v x → ∃ a : L, (∀ σ : G, σ • a = a) ∧ 1 ≤ v (x - a)

namespace LocData

variable {G L} (D : LocData G L)

theorem v_sub_smul_nonneg (σ : G) {x : L} (hx : 0 ≤ D.v x) : 0 ≤ D.v (σ • x - x) :=
  D.v.map_le_sub (by rw [D.v_smul]; exact hx) hx

/-- Successive approximation through `res`, the key estimate: for `ϖH ∈ L^H` with `v ϖH = e` and `res` at
level `e` on `L^H`, `v(σ ϖH - ϖH) ≤ v(σ x - x)` for integral `x ∈ L^H`. -/
theorem lb (H : Subgroup G) (e : ℕ) (he : 1 ≤ e) {ϖH : L} (hfix : ∀ h ∈ H, h • ϖH = ϖH)
    (hv : D.v ϖH = e)
    (resH : ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
      ∃ a : L, (∀ σ : G, σ • a = a) ∧ (e : WithTop ℤ) ≤ D.v (x - a))
    (σ : G) {x : L} (hxH : ∀ h ∈ H, h • x = x) (hx : 0 ≤ D.v x) :
    D.v (σ • ϖH - ϖH) ≤ D.v (σ • x - x) := by
  set V := D.v (σ • ϖH - ϖH)
  have hne : ϖH ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact WithTop.top_ne_coe hv
  have hϖ0 : 0 ≤ D.v ϖH := by rw [hv]; exact_mod_cast Nat.zero_le e
  have hV0 : 0 ≤ V := D.v_sub_smul_nonneg σ hϖ0
  have step : ∀ n : ℕ, ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
      min V (n : WithTop ℤ) ≤ D.v (σ • x - x) := by
    intro n
    induction n with
    | zero =>
      intro x _ hx
      exact (min_le_right _ _).trans (by exact_mod_cast D.v_sub_smul_nonneg σ hx)
    | succ n ih =>
      intro x hxH hx
      obtain ⟨a, ha, hva⟩ := resH x hxH hx
      set y := (x - a) * ϖH⁻¹ with hy
      have hxy : x = a + ϖH * y := by rw [hy]; field_simp; ring
      have hyH : ∀ h ∈ H, h • y = y := fun h hh => by
        rw [hy, smul_mul', smul_sub, smul_inv'', hxH h hh, ha h, hfix h hh]
      have hy0 : 0 ≤ D.v y := by
        have h1 : D.v (x - a) = e + D.v y := by
          rw [show x - a = ϖH * y by rw [hxy]; ring, AddValuation.map_mul, hv]
        rw [h1] at hva
        have h2 : (e : WithTop ℤ) + 0 ≤ (e : WithTop ℤ) + D.v y := by rwa [add_zero]
        exact (WithTop.add_le_add_iff_left (WithTop.natCast_ne_top e)).1 h2
      have hσx : σ • x - x = (σ • ϖH - ϖH) * (σ • y) + ϖH * (σ • y - y) := by
        rw [hxy, smul_add, smul_mul', ha σ]; ring
      rw [hσx]
      refine le_trans ?_ (D.v.map_add _ _)
      refine le_min ?_ ?_
      · rw [AddValuation.map_mul, D.v_smul]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right hy0)
      · rw [AddValuation.map_mul, hv]
        have := ih y hyH hy0
        calc min V ((n + 1 : ℕ) : WithTop ℤ) ≤ (e : WithTop ℤ) + min V (n : WithTop ℤ) := by
              rcases min_choice V (n : WithTop ℤ) with h | h <;> rw [h]
              · exact (min_le_left _ _).trans (le_add_of_nonneg_left (by exact_mod_cast Nat.zero_le e))
              · refine (min_le_right _ _).trans ?_
                rw [← Nat.cast_add]; exact_mod_cast (by omega : n + 1 ≤ e + n)
          _ ≤ (e : WithTop ℤ) + D.v (σ • y - y) := add_le_add le_rfl this
  rcases eq_or_ne V ⊤ with hVt | hVt
  · have hall : ∀ n : ℕ, (n : WithTop ℤ) ≤ D.v (σ • x - x) := fun n => by
      have h := step n x hxH hx
      rwa [hVt, min_eq_right le_top] at h
    rw [eq_top_of_forall_nat_le hall]; exact le_top
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hVt
    have hm0 : 0 ≤ m := by rw [← hm] at hV0; exact_mod_cast hV0
    have h := step m.toNat x hxH hx
    have hc : ((m.toNat : ℕ) : WithTop ℤ) = (m : WithTop ℤ) := by
      rw [← WithTop.coe_natCast, Int.toNat_of_nonneg hm0]
    rw [← hm, hc, min_self] at h
    rw [← hm]; exact h

theorem mem_bot_fix (x : L) : ∀ h ∈ (⊥ : Subgroup G), h • x = x := fun h hh => by
  rw [Subgroup.mem_bot.1 hh, one_smul]

/-- `v(σ ϖ - ϖ) ≤ v(σ x - x)` for all integral `x`, for any uniformizer `ϖ'`. -/
theorem lb_bot {ϖ' : L} (hv : D.v ϖ' = 1) (σ : G) {x : L} (hx : 0 ≤ D.v x) :
    D.v (σ • ϖ' - ϖ') ≤ D.v (σ • x - x) :=
  D.lb ⊥ 1 le_rfl (mem_bot_fix ϖ') (by rw [hv]; rfl)
    (fun x _ hx => by obtain ⟨a, ha, h⟩ := D.res x hx; exact ⟨a, ha, by exact_mod_cast h⟩) σ
    (mem_bot_fix x) hx

/-- Independence of the uniformizer. -/
theorem v_unif_eq {ϖ₁ ϖ₂ : L} (h₁ : D.v ϖ₁ = 1) (h₂ : D.v ϖ₂ = 1) (σ : G) :
    D.v (σ • ϖ₁ - ϖ₁) = D.v (σ • ϖ₂ - ϖ₂) :=
  le_antisymm (D.lb_bot h₁ σ (by rw [h₂]; exact zero_le_one))
    (D.lb_bot h₂ σ (by rw [h₁]; exact zero_le_one))

theorem v_inv_nonneg {x : L} (hx : D.v x < 0) : 0 ≤ D.v x⁻¹ := by
  rw [AddValuation.map_inv]
  induction hvx : D.v x with
  | top => rw [hvx] at hx; exact absurd hx (not_lt.2 le_top)
  | coe m =>
    rw [hvx] at hx
    have : m < 0 := by exact_mod_cast hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact_mod_cast (by omega : (0 : ℤ) ≤ -m)

theorem eq_one_of_fix_ϖ {σ : G} (h : σ • D.ϖ = D.ϖ) : σ = 1 := by
  have hO : ∀ x : L, 0 ≤ D.v x → σ • x = x := fun x hx => by
    have := D.lb_bot D.v_ϖ σ hx
    rw [h, sub_self, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact sub_eq_zero.1 this
  refine D.faithful σ fun x => ?_
  rcases le_or_gt 0 (D.v x) with hx | hx
  · exact hO x hx
  · have := hO x⁻¹ (D.v_inv_nonneg hx)
    rw [smul_inv''] at this
    exact inv_injective this

/-- The ramification function `i(σ) = v(σ ϖ - ϖ)`. -/
def ramFn : RamFn G where
  i σ := toENat (D.v (σ • D.ϖ - D.ϖ))
  i_eq_top σ := by
    rw [toENat_eq_top_iff, AddValuation.top_iff, sub_eq_zero]
    exact ⟨D.eq_one_of_fix_ϖ, fun h => by rw [h, one_smul]⟩
  one_le σ := by
    have : (1 : WithTop ℤ) ≤ D.v (σ • D.ϖ - D.ϖ) :=
      D.v.map_le_sub (by rw [D.v_smul, D.v_ϖ]) (by rw [D.v_ϖ])
    have h2 := toENat_mono this
    rwa [show toENat 1 = 1 from rfl] at h2
  le_mul σ τ := by
    rw [← toENat_mono.map_min]
    apply toENat_mono
    have : (σ * τ) • D.ϖ - D.ϖ = σ • (τ • D.ϖ - D.ϖ) + (σ • D.ϖ - D.ϖ) := by
      rw [mul_smul, smul_sub]; ring
    rw [this, min_comm]
    refine le_trans ?_ (D.v.map_add _ _)
    rw [D.v_smul]
  i_inv σ := by
    congr 1
    have : σ⁻¹ • D.ϖ - D.ϖ = σ⁻¹ • (D.ϖ - σ • D.ϖ) := by
      rw [smul_sub, inv_smul_smul]
    rw [this, D.v_smul, AddValuation.map_sub_swap]
  i_conj σ τ := by
    congr 1
    have : (τ * σ * τ⁻¹) • D.ϖ - D.ϖ = τ • (σ • (τ⁻¹ • D.ϖ) - τ⁻¹ • D.ϖ) := by
      rw [mul_smul, mul_smul, smul_sub, smul_inv_smul]
    rw [this, D.v_smul]
    exact D.v_unif_eq (by rw [D.v_smul, D.v_ϖ]) D.v_ϖ σ

theorem ramFn_i (σ : G) : D.ramFn.i σ = toENat (D.v (σ • D.ϖ - D.ϖ)) := rfl

/-- `i(σ)` through any uniformizer. -/
theorem ramFn_i_of_unif {ϖ' : L} (h : D.v ϖ' = 1) (σ : G) :
    D.ramFn.i σ = toENat (D.v (σ • ϖ' - ϖ')) := by
  rw [ramFn_i, D.v_unif_eq D.v_ϖ h]

end LocData

end

end Swan
end RamanujanPetersson

end Inline_Swan_Loc

section Inline_Swan_GlobV


/-!
# S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group

For a Dedekind domain `S` with fraction field `L` and a height-one prime `P`, `adicAdd P` is the `P`-adic
valuation of `L` as an `AddValuation L (WithTop ℤ)` (`-log` of Mathlib's multiplicative `P.valuation L`).
It has a uniformizer, integral elements are approximated by elements of `S` modulo `P`, and it is invariant
under every automorphism of `S` (compatibly extended to `L`) that stabilizes `P`.

If a finite group `G` is a Galois group for `S / R` (`IsGaloisGroup G R S`) and `S ⧸ P` is finite, every element
of `S` is congruent mod `P` to an element fixed by the inertia group `I = P.inertia G` (the residue field
extension of `S` over `S^I` is trivial: `card_stabilizer_eq_card_inertia_mul_finrank` with stabilizer = inertia
= `I`). Hence `(I, L, adicAdd P)` is local data (`inertiaLocData`), so `Swan.LocData.ramFn` applies.
-/



open IsDedekindDomain WithZero
open scoped Pointwise

namespace RamanujanPetersson.Swan

theorem withTop_eq_of_natCast_le_iff {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, (n : WithTop ℤ) ≤ a ↔ (n : WithTop ℤ) ≤ b) : a = b := by
  induction a with
  | top =>
    induction b with
    | top => rfl
    | coe b =>
      have := (h (b.toNat + 1)).1 le_top
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
      omega
  | coe a =>
    induction b with
    | top =>
      have := (h (a.toNat + 1)).2 le_top
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
      omega
    | coe b =>
      have ha' : 0 ≤ a := by exact_mod_cast ha
      have hb' : 0 ≤ b := by exact_mod_cast hb
      have h1 := (h a.toNat).1 (by rw [← WithTop.coe_natCast, WithTop.coe_le_coe]; omega)
      have h2 := (h b.toNat).2 (by rw [← WithTop.coe_natCast, WithTop.coe_le_coe]; omega)
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at h1 h2
      congr 1
      omega

section AdicAdd

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)

open Classical in
/-- `-log` of the `P`-adic valuation, with `⊤` at `0`. -/
def negLogV (x : L) : WithTop ℤ :=
  if x = 0 then ⊤ else ((-log (P.valuation L x) : ℤ) : WithTop ℤ)

theorem negLogV_of_ne {x : L} (hx : x ≠ 0) :
    negLogV P x = ((-log (P.valuation L x) : ℤ) : WithTop ℤ) := if_neg hx

theorem negLogV_zero : negLogV P (0 : L) = ⊤ := if_pos rfl

theorem negLogV_mul (x y : L) : negLogV P (x * y) = negLogV P x + negLogV P y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, negLogV_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, negLogV_zero, WithTop.add_top]
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [negLogV_of_ne P (mul_ne_zero hx hy), negLogV_of_ne P hx, negLogV_of_ne P hy, map_mul,
    log_mul h1 h2, neg_add, WithTop.coe_add]

theorem negLogV_add (x y : L) : min (negLogV P x) (negLogV P y) ≤ negLogV P (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]; exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero]; exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, negLogV_zero]; exact le_top
  have h := Valuation.map_add (P.valuation L) x y
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have h3 : P.valuation L (x + y) ≠ 0 := (Valuation.ne_zero_iff _).2 hxy
  rw [← exp_log h1, ← exp_log h2, ← exp_log h3, le_max_iff, exp_le_exp, exp_le_exp] at h
  rw [negLogV_of_ne P hx, negLogV_of_ne P hy, negLogV_of_ne P hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  rcases h with h | h
  · exact min_le_of_left_le (by omega)
  · exact min_le_of_right_le (by omega)

/-- The `P`-adic valuation of `L = Frac S` as an additive valuation with values in `ℤ ∪ {⊤}`. -/
def adicAdd : AddValuation L (WithTop ℤ) :=
  AddValuation.of (negLogV P) (negLogV_zero P)
    (by rw [negLogV_of_ne P one_ne_zero, map_one, log_one, neg_zero, WithTop.coe_zero])
    (negLogV_add P) (negLogV_mul P)

theorem adicAdd_apply (x : L) : adicAdd P x = negLogV P x := rfl

theorem natCast_le_adicAdd_iff (x : L) (n : ℕ) :
    (n : WithTop ℤ) ≤ adicAdd P x ↔ P.valuation L x ≤ exp (-(n : ℤ)) := by
  rw [adicAdd_apply]
  by_cases hx : x = 0
  · rw [hx, negLogV_zero, map_zero]; exact ⟨fun _ => zero_le, fun _ => le_top⟩
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [negLogV_of_ne P hx, ← WithTop.coe_natCast, WithTop.coe_le_coe]
  conv_rhs => rw [← exp_log h1]
  rw [exp_le_exp]
  constructor <;> intro h <;> omega

theorem natCast_le_adicAdd_algebraMap_iff (r : S) (n : ℕ) :
    (n : WithTop ℤ) ≤ adicAdd P (algebraMap S L r) ↔ r ∈ P.asIdeal ^ n := by
  rw [natCast_le_adicAdd_iff, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_mem]

theorem adicAdd_nonneg_iff (x : L) : 0 ≤ adicAdd P x ↔ P.valuation L x ≤ 1 := by
  have := natCast_le_adicAdd_iff P x 0
  simpa using this

theorem adicAdd_algebraMap_nonneg (r : S) : 0 ≤ adicAdd P (algebraMap S L r) := by
  have := (natCast_le_adicAdd_algebraMap_iff (L := L) P r 0).2 (by simp)
  simpa using this

theorem one_le_adicAdd_algebraMap_iff (r : S) :
    1 ≤ adicAdd P (algebraMap S L r) ↔ r ∈ P.asIdeal := by
  have := natCast_le_adicAdd_algebraMap_iff (L := L) P r 1
  simpa using this

variable (L) in
theorem exists_adicAdd_eq_one : ∃ π : L, adicAdd P π = 1 := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  refine ⟨π, ?_⟩
  rw [adicAdd_apply, negLogV_of_ne P h0, hπ, log_exp, neg_neg, WithTop.coe_one]

theorem exists_one_le_adicAdd_sub {x : L} (hx : 0 ≤ adicAdd P x) :
    ∃ r : S, 1 ≤ adicAdd P (x - algebraMap S L r) := by
  obtain ⟨r, hr⟩ := P.exists_valuation_sub_lt_of_integer ((adicAdd_nonneg_iff P x).1 hx) 1
  refine ⟨r, ?_⟩
  have key : P.valuation L (algebraMap S L r - x) ≤ exp (-((1 : ℕ) : ℤ)) := by
    by_cases h0 : P.valuation L (algebraMap S L r - x) = 0
    · rw [h0]; exact zero_le
    rw [Units.val_one] at hr
    rw [← exp_log h0] at hr ⊢
    rw [← exp_zero, exp_lt_exp] at hr
    rw [exp_le_exp]
    omega
  have := (natCast_le_adicAdd_iff P _ 1).2 key
  rw [← AddValuation.map_neg, neg_sub] at this
  simpa using this

section Smul

variable {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

/-- `adicAdd P` is invariant under every `σ` with `σ • P = P`. -/
theorem adicAdd_smul (σ : G) (hσ : σ • P.asIdeal = P.asIdeal) (x : L) :
    adicAdd P (σ • x) = adicAdd P x := by
  have hpow : ∀ n : ℕ, σ • (P.asIdeal ^ n) = P.asIdeal ^ n := fun n => by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, hσ]
  have hint : ∀ r : S, adicAdd P (algebraMap S L (σ • r)) = adicAdd P (algebraMap S L r) := by
    intro r
    refine withTop_eq_of_natCast_le_iff (adicAdd_algebraMap_nonneg P _)
      (adicAdd_algebraMap_nonneg P _) (fun n => ?_)
    rw [natCast_le_adicAdd_algebraMap_iff, natCast_le_adicAdd_algebraMap_iff]
    conv_lhs => rw [← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  rw [smul_div₀', hc, hc, AddValuation.map_div, AddValuation.map_div, hint, hint]

end Smul

end AdicAdd

section Residue

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

include R in
attribute [local instance] Ideal.Quotient.field in
/-- Every element of `S` is congruent mod `Q` to an element fixed by the inertia group of `Q`. -/
theorem exists_inertia_fixed_sub_mem (Q : Ideal S) [Q.IsMaximal] [Finite (S ⧸ Q)] (b : S) :
    ∃ a : S, (∀ σ ∈ Q.inertia G, σ • a = a) ∧ b - a ∈ Q := by
  set I := Q.inertia G with hI
  let A := FixedPoints.subalgebra R S I
  haveI : Algebra.IsInvariant A S I := IsGaloisGroup.isInvariant
  haveI : Algebra.IsIntegral A S := Algebra.IsInvariant.isIntegral A S I
  let p := Q.under A
  have : Finite (A ⧸ p) :=
    Finite.of_injective (algebraMap (A ⧸ p) (S ⧸ Q)) (RingHom.injective _)
  have : Finite p.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField p).2
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := I) p Q
  have hinert : Q.inertia I = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true]
    exact σ.2
  rw [hinert, Subgroup.card_top] at hcard
  have hle : Nat.card I * Q.inertiaDeg A ≤ Nat.card I * 1 := by
    rw [mul_one, ← hcard]; exact Subgroup.card_le_card_group _
  rw [Ideal.inertiaDeg_eq_of_isMaximal p Q] at hle
  haveI : Module.Finite (A ⧸ p) (S ⧸ Q) := Module.Finite.of_finite
  haveI : Module.Free (A ⧸ p) (S ⧸ Q) := Module.Free.of_divisionRing _ _
  have hpos : 0 < Module.finrank (A ⧸ p) (S ⧸ Q) := Module.finrank_pos
  have h1 : Module.finrank (A ⧸ p) (S ⧸ Q) = 1 := by
    have := Nat.le_of_mul_le_mul_left hle Nat.card_pos
    omega
  have hsurj : Function.Surjective (algebraMap (A ⧸ p) (S ⧸ Q)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
  obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk Q b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨(a : S), fun σ hσ => a.2 ⟨σ, hσ⟩, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Ideal.Quotient.algebraMap_mk_of_liesOver]
  rfl

end Residue

section Inertia

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

include R in
/-- The inertia group of `Q` acting on `L` with the `Q`-adic valuation is local data. -/
def inertiaLocData : LocData (Q.asIdeal.inertia G) L where
  v := adicAdd Q
  v_smul σ x := adicAdd_smul Q hc (σ : G)
    (MulAction.mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer Q.asIdeal σ.2)) x
  faithful σ hσ := by
    have : FaithfulSMul G S := IsGaloisGroup.faithful R
    apply Subtype.ext
    show (σ : G) = 1
    apply eq_of_smul_eq_smul (α := S)
    intro s
    apply IsFractionRing.injective S L
    rw [one_smul, ← hc]
    exact hσ (algebraMap S L s)
  ϖ := Classical.choose (exists_adicAdd_eq_one L Q)
  v_ϖ := Classical.choose_spec (exists_adicAdd_eq_one L Q)
  res x hx := by
    obtain ⟨r, hr⟩ := exists_one_le_adicAdd_sub Q hx
    obtain ⟨a, ha, hra⟩ := exists_inertia_fixed_sub_mem (R := R) (G := G) Q.asIdeal r
    refine ⟨algebraMap S L a, fun σ => ?_, ?_⟩
    · show (σ : G) • algebraMap S L a = _
      rw [hc, ha σ σ.2]
    · have h2 : (1 : WithTop ℤ) ≤ adicAdd Q (algebraMap S L r - algebraMap S L a) := by
        rw [← map_sub]
        exact (one_le_adicAdd_algebraMap_iff Q (r - a)).2 hra
      have e : x - algebraMap S L a =
          (x - algebraMap S L r) + (algebraMap S L r - algebraMap S L a) := by ring
      rw [e]
      exact le_trans (le_min hr h2) ((adicAdd Q).map_add _ _)

theorem inertiaLocData_v : (inertiaLocData (R := R) hc Q).v = adicAdd Q := rfl

end Inertia

end RamanujanPetersson.Swan

end Inline_Swan_GlobV

section Inline_Swan_GlobF


/-!
# S4-Swan (K2), part 15: fixed rings of Dedekind domains, and fixed fractions

* `isDedekindDomain_fixed`: if `S` is a Dedekind domain, finite and torsion-free over a Dedekind domain `R`, and
  `H` is a group of `R`-automorphisms of `S`, then the fixed ring `S^H = FixedPoints.subalgebra R S H` is a
  Dedekind domain (Noetherian as an `R`-submodule of `S`, dimension one as an integral extension of `R`,
  integrally closed because `S` is and `H` fixes the integral closure inside `Frac (S^H)`), and `S` is finite
  over it.
* `exists_fixed_mul_eq`: for a finite group `H` acting compatibly on `S` and `L = Frac S`, every `H`-fixed
  `x ∈ L` is a quotient of `H`-fixed elements of `S` (multiply by the norm `∏_h h b` of a denominator `b`).
-/



namespace RamanujanPetersson.Swan

section FixedRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (H : Subgroup G)

theorem mem_fixedSubalgebra_iff (s : S) :
    s ∈ FixedPoints.subalgebra R S H ↔ ∀ h : H, h • s = s := Iff.rfl

variable [Module.Finite R S]

theorem isIntegral_fixedSubalgebra :
    Algebra.IsIntegral R (FixedPoints.subalgebra R S H) :=
  Algebra.IsIntegral.of_injective (FixedPoints.subalgebra R S H).val Subtype.val_injective

theorem finite_fixed : Module.Finite (FixedPoints.subalgebra R S H) S :=
  Module.Finite.of_restrictScalars_finite R _ S

variable [IsDedekindDomain R] [IsDedekindDomain S]

/-- The fixed ring of a group of automorphisms of a finite Dedekind extension is Dedekind. -/
theorem isDedekindDomain_fixed : IsDedekindDomain (FixedPoints.subalgebra R S H) := by
  set A := FixedPoints.subalgebra R S H
  have hN : IsNoetherian R A := isNoetherian_of_injective A.val.toLinearMap Subtype.val_injective
  have : Algebra.IsIntegral R A := isIntegral_fixedSubalgebra H
  refine (isDedekindDomain_iff A (FractionRing A)).2 ⟨inferInstance, isNoetherian_of_tower R hN,
    Ring.DimensionLEOne.of_isIntegral R A, ?_⟩
  intro x hx
  let FS := FractionRing S
  have hinj : Function.Injective (algebraMap A FS) := by
    rw [IsScalarTower.algebraMap_eq A S FS]
    exact (IsFractionRing.injective S FS).comp Subtype.val_injective
  let f : FractionRing A →ₐ[A] FS := IsFractionRing.liftAlgHom (g := Algebra.ofId A FS) hinj
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.tower_top (A := S) (hx.map f))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : (b : S) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have hfab : f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) =
      algebraMap S FS a / algebraMap S FS b := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply A S FS,
      IsScalarTower.algebraMap_apply A S FS]
    rfl
  have hsb : s * b = a := by
    apply IsFractionRing.injective S FS
    have hb' : algebraMap S FS b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S FS)).2 hb0
    rw [map_mul, hs, hfab, div_mul_cancel₀ _ hb']
  have hfix : ∀ σ : H, σ • s = s := by
    intro σ
    have h1 : σ • (s * (b : S)) = s * b := by rw [hsb]; exact a.2 σ
    rw [smul_mul', b.2 σ] at h1
    exact mul_right_cancel₀ hb0 h1
  refine ⟨⟨s, hfix⟩, f.toRingHom.injective ?_⟩
  change f (algebraMap A (FractionRing A) ⟨s, hfix⟩) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A S FS]
  exact hs

end FixedRing

section NormTrick

variable {S : Type*} [CommRing S] [IsDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (H : Subgroup G) [Finite H]
include hc

/-- An `H`-fixed element of `L = Frac S` is a quotient of `H`-fixed elements of `S`. -/
theorem exists_fixed_mul_eq (x : L) (hx : ∀ h ∈ H, h • x = x) :
    ∃ c1 c2 : S, (∀ h ∈ H, h • c1 = c1) ∧ (∀ h ∈ H, h • c2 = c2) ∧ c2 ≠ 0 ∧
      x * algebraMap S L c2 = algebraMap S L c1 := by
  classical
  letI := Fintype.ofFinite H
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap S L b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).2 hb0
  set P : S := ∏ h ∈ Finset.univ.erase (1 : H), (h : G) • b with hP
  have hc2 : ∏ h : H, (h : G) • b = b * P := by
    rw [hP, ← Finset.mul_prod_erase Finset.univ (fun h : H => (h : G) • b) (Finset.mem_univ 1)]
    simp
  have hfix2 : ∀ g ∈ H, g • ∏ h : H, (h : G) • b = ∏ h : H, (h : G) • b := by
    intro g hg
    rw [Finset.smul_prod']
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : H)) _ _ (fun h => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_mk, mul_smul]
  have hmul : algebraMap S L a / algebraMap S L b * algebraMap S L (∏ h : H, (h : G) • b) =
      algebraMap S L (a * P) := by
    rw [hc2, map_mul, map_mul, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hb']
  refine ⟨a * P, ∏ h : H, (h : G) • b, fun g hg => ?_, hfix2, ?_, hmul⟩
  · apply IsFractionRing.injective S L
    rw [← hc, ← hmul, smul_mul', hx g hg, hc, hfix2 g hg]
  · rw [Finset.prod_ne_zero_iff]
    exact fun h _ => (smul_ne_zero_iff_ne _).2 hb0

end NormTrick

end RamanujanPetersson.Swan

end Inline_Swan_GlobF

section Inline_GOS_A_Ord


/-!
# S4-GOS-A, part 1: the exponent of a height-one prime in an ideal

For a height-one prime `Q` of a Dedekind domain `S`, `ordI Q J` is the exponent of `Q` in the factorization of
the ideal `J` (the exponent in Mathlib's `Q.intValuation`). Multiplicativity, the membership criterion
`n ≤ ordI Q (span {x}) ↔ x ∈ Q ^ n`, products of principal ideals, uniformizers (`ordI = 1`), and one step of
`Q`-adic approximation by multiples of `ϖ ^ n`.
-/



open IsDedekindDomain WithZero
open scoped Classical

namespace RamanujanPetersson.GOS

section Ord

variable {S : Type*} [CommRing S] [IsDedekindDomain S] (Q : HeightOneSpectrum S)

/-- The exponent of `Q` in the factorization of an ideal `J`. -/
def ordI (J : Ideal S) : ℕ := (Associates.mk Q.asIdeal).count (Associates.mk J).factors

theorem ordI_mul {J J' : Ideal S} (hJ : J ≠ ⊥) (hJ' : J' ≠ ⊥) :
    ordI Q (J * J') = ordI Q J + ordI Q J' := by
  unfold ordI
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.2 hJ) (Associates.mk_ne_zero.2 hJ')
    (Associates.irreducible_mk.2 Q.irreducible)

theorem ordI_eq_zero_iff {J : Ideal S} (hJ : J ≠ ⊥) : ordI Q J = 0 ↔ ¬ J ≤ Q.asIdeal := by
  rw [← Ideal.dvd_iff_le, ← Associates.count_ne_zero_iff_dvd hJ Q.irreducible, not_not]
  rfl

theorem le_ordI_iff {J : Ideal S} (hJ : J ≠ ⊥) (n : ℕ) : n ≤ ordI Q J ↔ J ≤ Q.asIdeal ^ n := by
  unfold ordI
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hJ)
    (Associates.irreducible_mk.2 Q.irreducible), ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le]

theorem ordI_top : ordI Q ⊤ = 0 :=
  (ordI_eq_zero_iff Q top_ne_bot).2 fun h => Q.isPrime.ne_top (top_le_iff.1 h)

omit [IsDedekindDomain S] in
theorem span_ne_bot {x : S} (hx : x ≠ 0) : Ideal.span {x} ≠ ⊥ := by
  rwa [ne_eq, Ideal.span_singleton_eq_bot]

theorem le_ordI_span_iff {x : S} (hx : x ≠ 0) (n : ℕ) :
    n ≤ ordI Q (Ideal.span {x}) ↔ x ∈ Q.asIdeal ^ n := by
  rw [le_ordI_iff Q (span_ne_bot hx), Ideal.span_singleton_le_iff_mem]

theorem ordI_span_prod {ι : Type*} (s : Finset ι) (f : ι → S) (hf : ∀ i ∈ s, f i ≠ 0) :
    ordI Q (Ideal.span {∏ i ∈ s, f i}) = ∑ i ∈ s, ordI Q (Ideal.span {f i}) := by
  induction s using Finset.induction_on with
  | empty => simp [Ideal.span_singleton_one, ordI_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← Ideal.span_singleton_mul_span_singleton,
      ordI_mul Q (span_ne_bot (hf a (Finset.mem_insert_self a s)))
        (span_ne_bot (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem intValuation_eq_exp_ordI {x : S} (hx : x ≠ 0) :
    Q.intValuation x = exp (-(ordI Q (Ideal.span {x}) : ℤ)) :=
  Q.intValuation_if_neg hx

theorem ordI_span_eq_one {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    ordI Q (Ideal.span {ϖ}) = 1 := by
  have hϖ : ϖ ≠ 0 := by rintro rfl; exact h2 (Ideal.zero_mem _)
  have a := (le_ordI_span_iff Q hϖ 1).2 (by rwa [pow_one])
  have b := mt (le_ordI_span_iff Q hϖ 2).1 h2
  omega

theorem ordI_span_pow {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (n : ℕ) :
    ordI Q (Ideal.span {ϖ ^ n}) = n := by
  have hϖ : ϖ ≠ 0 := by rintro rfl; exact h2 (Ideal.zero_mem _)
  have := ordI_span_prod Q (Finset.range n) (fun _ => ϖ) (fun _ _ => hϖ)
  simpa [Finset.prod_const, ordI_span_eq_one Q h1 h2] using this

theorem exists_unif : ∃ ϖ : S, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  refine ⟨π, ?_, ?_⟩
  · rw [← pow_one Q.asIdeal, ← Q.intValuation_le_pow_iff_mem, hπ]; simp
  · rw [← Q.intValuation_le_pow_iff_mem, hπ, exp_le_exp]; norm_num

/-- One step of `Q`-adic approximation by multiples of `ϖ ^ n`. -/
theorem exists_sub_mul_pow_mem {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) {x : S}
    {n : ℕ} (hx : x ∈ Q.asIdeal ^ n) : ∃ y : S, x - y * ϖ ^ n ∈ Q.asIdeal ^ (n + 1) := by
  have hϖ : ϖ ≠ 0 := by rintro rfl; exact h2 (Ideal.zero_mem _)
  have hv : Q.intValuation x ≤ Q.intValuation (ϖ ^ n) :=
    ((Q.intValuation_le_pow_iff_mem x n).2 hx).trans_eq
      (by rw [intValuation_eq_exp_ordI Q (pow_ne_zero n hϖ), ordI_span_pow Q h1 h2])
  obtain ⟨y, hy⟩ := Q.exists_intValuation_mul_sub_lt hv (Multiplicative.ofAdd (-((n + 1 : ℕ) : ℤ)))
  exact ⟨y, (Q.intValuation_le_pow_iff_mem _ _).1 hy.le⟩

end Ord

end RamanujanPetersson.GOS

end Inline_GOS_A_Ord

section Inline_GOS_A_Gen


/-!
# S4-GOS-A, part 2: the conductor of `A[ϖ]` in a totally ramified extension

`S / A` is a finite torsion-free extension of Dedekind domains with Galois group `G` (`IsGaloisGroup G A S`) and
`Q` is a height-one prime of `S` with finite residue field whose inertia group is all of `G` (`hI`). Then `Q` is the
only prime of `S` over `q = Q ∩ A` (`eq_of_map_le`), so `Q ^ k ⊆ q S` for some `k`; every element of `S` is
`Q`-adically approximated by `A[ϖ]` for a uniformizer `ϖ` (`exists_adjoin_sub_mem`, residue field of `S` = that of
`A` by `Swan.exists_inertia_fixed_sub_mem`), and Nakayama over `q` gives `t ∈ A \ q` with `t S ⊆ A[ϖ]`, i.e. the
conductor of `A[ϖ]` is prime to `Q` (`exists_mem_conductor_not_mem`). No completion is used.
-/



open IsDedekindDomain WithZero
open scoped Classical Pointwise

namespace RamanujanPetersson.GOS

section Tot

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G A S]
  (Q : HeightOneSpectrum S) (hI : ∀ σ : G, σ ∈ Q.asIdeal.inertia G)

omit [IsDedekindDomain A] [Module.Finite A S] [Module.IsTorsionFree A S] in
include hI in
theorem exists_algebraMap_sub_mem [Finite (S ⧸ Q.asIdeal)] (y : S) :
    ∃ a : A, y - algebraMap A S a ∈ Q.asIdeal := by
  have := Q.isMaximal
  obtain ⟨b, hb, hyb⟩ := Swan.exists_inertia_fixed_sub_mem (R := A) (G := G) Q.asIdeal y
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b (fun σ => hb σ (hI σ))
  exact ⟨a, hyb⟩

omit [IsDedekindDomain A] [Module.Finite A S] [Module.IsTorsionFree A S] in
include hI in
theorem exists_adjoin_sub_mem [Finite (S ⧸ Q.asIdeal)] {ϖ : S} (h1 : ϖ ∈ Q.asIdeal)
    (h2 : ϖ ∉ Q.asIdeal ^ 2) (n : ℕ) (s : S) :
    ∃ m ∈ Algebra.adjoin A {ϖ}, s - m ∈ Q.asIdeal ^ n := by
  induction n with
  | zero => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm, hsm⟩ := ih
    obtain ⟨y, hy⟩ := exists_sub_mul_pow_mem Q h1 h2 hsm
    obtain ⟨a, ha⟩ := exists_algebraMap_sub_mem (A := A) Q hI y
    have hϖm : ϖ ∈ Algebra.adjoin A {ϖ} := Algebra.self_mem_adjoin_singleton A ϖ
    refine ⟨m + algebraMap A S a * ϖ ^ n, Subalgebra.add_mem _ hm (Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ a) (Subalgebra.pow_mem _ hϖm n)), ?_⟩
    have e : s - (m + algebraMap A S a * ϖ ^ n) =
        (s - m - y * ϖ ^ n) + (y - algebraMap A S a) * ϖ ^ n := by ring
    rw [e]
    refine Ideal.add_mem _ hy ?_
    have := Ideal.mul_mem_mul ha (Ideal.pow_mem_pow h1 n)
    rwa [← pow_succ'] at this

omit [Module.IsTorsionFree A S] in
include hI in
/-- In the totally ramified case `Q` is the only prime of `S` over `Q ∩ A`. -/
theorem eq_of_map_le (P : Ideal S) [P.IsPrime]
    (hP : (Q.under A).asIdeal.map (algebraMap A S) ≤ P) : P = Q.asIdeal := by
  have hq := (Q.under A).isMaximal
  have hle : (Q.under A).asIdeal ≤ P.under A := Ideal.map_le_iff_le_comap.1 hP
  have heq : P.under A = (Q.under A).asIdeal :=
    (hq.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have : P.LiesOver (Q.under A).asIdeal := ⟨heq.symm⟩
  have : Q.asIdeal.LiesOver (Q.under A).asIdeal := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under A).asIdeal Q.asIdeal P G
  rw [← hσ]
  exact MulAction.mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer Q.asIdeal (hI σ))

include hI in
theorem exists_pow_le_map : ∃ k : ℕ, Q.asIdeal ^ k ≤ (Q.under A).asIdeal.map (algebraMap A S) := by
  have := Q.isMaximal
  have hne : (Q.under A).asIdeal.map (algebraMap A S) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A S)).not.mpr
      (Q.under A).ne_bot
  obtain ⟨J, hQJ, heq⟩ := Ideal.eq_prime_pow_mul_coprime hne Q.asIdeal
  have hJ : J = ⊤ := by
    by_contra hJ
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
    have hMQ : M = Q.asIdeal := eq_of_map_le Q hI M (by rw [heq]; exact Ideal.mul_le_right.trans hJM)
    exact Q.isPrime.ne_top (top_le_iff.1 (hQJ ▸ sup_le le_rfl (hMQ ▸ hJM)))
  rw [hJ, Ideal.mul_top] at heq
  exact ⟨_, heq.symm.le⟩

include hI in
/-- The conductor of `A[ϖ]` in `S` is prime to `Q` (Nakayama over `Q ∩ A`). -/
theorem exists_mem_conductor_not_mem [Finite (S ⧸ Q.asIdeal)] {ϖ : S} (h1 : ϖ ∈ Q.asIdeal)
    (h2 : ϖ ∉ Q.asIdeal ^ 2) : ∃ t ∈ conductor A ϖ, t ∉ Q.asIdeal := by
  obtain ⟨k, hk⟩ := exists_pow_le_map (A := A) Q hI
  let N : Submodule A S := Subalgebra.toSubmodule (Algebra.adjoin A {ϖ})
  have hfg : (⊤ : Submodule A (S ⧸ N)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule A (S ⧸ N)) ≤ (Q.under A).asIdeal • ⊤ := by
    rintro z -
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective N z
    obtain ⟨m, hm, hsm⟩ := exists_adjoin_sub_mem (A := A) Q hI h1 h2 k s
    have hw : s - m ∈ (Q.under A).asIdeal • (⊤ : Submodule A S) := by
      rw [Ideal.smul_top_eq_map]; exact hk hsm
    have e : (Submodule.Quotient.mk s : S ⧸ N) = N.mkQ (s - m) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq, sub_sub_cancel]
      exact hm
    rw [e]
    have := Submodule.mem_map_of_mem (f := N.mkQ) hw
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ ⊤ hfg hle
  refine ⟨algebraMap A S r, mem_conductor_iff.2 fun b => ?_, fun hr' => ?_⟩
  · have := hr (Submodule.Quotient.mk b) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def] at this
    exact this
  · have hr2 : r ∈ (Q.under A).asIdeal := hr'
    exact (Q.under A).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hr2 hr1))

end Tot

end RamanujanPetersson.GOS

end Inline_GOS_A_Gen

section Inline_GOS_A_Min


/-!
# S4-GOS-A, part 3: the minimal polynomial of an element with trivial stabilizer

`S / A` is a finite torsion-free extension of Dedekind domains with Galois group `G`. If `σ ϖ = ϖ` only for
`σ = 1`, then `minpoly A ϖ` maps to `∏_σ (X - σ ϖ)` (`minpoly_map_eq_charpoly`), has degree `|G|`,
`f'(ϖ) = ∏_{σ ≠ 1} (ϖ - σ ϖ)` (`aeval_derivative_minpoly`), and `ϖ` generates `Frac S` over `Frac A`
(`adjoin_eq_top`), the hypothesis of Mathlib's `conductor_mul_differentIdeal`.
-/



open Polynomial IntermediateField
open scoped Classical nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Min

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S] [IsGaloisGroup G A S]

omit [IsDedekindDomain A] [IsDedekindDomain S] [Module.Finite A S] [Module.IsTorsionFree A S]
  [Fintype G] in
theorem aeval_smul (σ : G) (f : A[X]) (x : S) : aeval (σ • x) f = σ • aeval x f := by
  have := IsGaloisGroup.commutes (G := G) (A := A) (B := S)
  have h := aeval_algHom_apply (MulSemiringAction.toAlgHom A S σ) x f
  simpa using h

variable {ϖ : S} (hst : ∀ σ : G, σ • ϖ = ϖ → σ = 1)

include hst in
/-- An element with trivial stabilizer has minimal polynomial `∏_σ (X - σ ϖ)`. -/
theorem minpoly_map_eq_charpoly :
    (minpoly A ϖ).map (algebraMap A S) = MulSemiringAction.charpoly G ϖ := by
  obtain ⟨p, hp, hdeg, hmon⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A S G ϖ) (MulSemiringAction.monic_charpoly G ϖ)
  have hint : IsIntegral A ϖ := Algebra.IsIntegral.isIntegral ϖ
  have hev : aeval ϖ p = 0 := by
    rw [aeval_def, ← eval_map, hp, MulSemiringAction.eval_charpoly]
  have hdvd : minpoly A ϖ ∣ p := minpoly.isIntegrallyClosed_dvd hint hev
  have hroot : ∀ σ : G, aeval (σ • ϖ) (minpoly A ϖ) = 0 := by
    intro σ; rw [aeval_smul, minpoly.aeval, smul_zero]
  have hinj : Function.Injective fun σ : G => σ • ϖ := by
    intro σ τ h
    have h' : (τ⁻¹ * σ) • ϖ = ϖ := by
      simp only at h
      rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.1 (hst _ h')).symm
  have hf0 : (minpoly A ϖ).map (algebraMap A S) ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hsub : (Finset.univ.image fun σ : G => σ • ϖ) ⊆
      ((minpoly A ϖ).map (algebraMap A S)).roots.toFinset := by
    intro y hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_map, ← aeval_def]
    exact hroot σ
  have hcard : Fintype.card G ≤ (minpoly A ϖ).natDegree := by
    calc Fintype.card G = (Finset.univ.image fun σ : G => σ • ϖ).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      _ ≤ ((minpoly A ϖ).map (algebraMap A S)).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card ((minpoly A ϖ).map (algebraMap A S)).roots := Multiset.toFinset_card_le _
      _ ≤ ((minpoly A ϖ).map (algebraMap A S)).natDegree := card_roots' _
      _ = (minpoly A ϖ).natDegree := (minpoly.monic hint).natDegree_map _
  have hdegp : p.natDegree = Fintype.card G := by
    rw [hdeg, MulSemiringAction.charpoly_eq, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
  have heq : p = minpoly A ϖ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd (hdegp ▸ hcard)
  rw [← heq, hp]

include hst in
theorem natDegree_minpoly : (minpoly A ϖ).natDegree = Fintype.card G := by
  have hint : IsIntegral A ϖ := Algebra.IsIntegral.isIntegral ϖ
  rw [← (minpoly.monic hint).natDegree_map (algebraMap A S), minpoly_map_eq_charpoly hst,
    MulSemiringAction.charpoly_eq, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]

include hst in
/-- Hilbert's formula for `f'(ϖ)`: `f'(ϖ) = ∏_{σ ≠ 1} (ϖ - σ ϖ)`. -/
theorem aeval_derivative_minpoly :
    aeval ϖ (derivative (minpoly A ϖ)) = ∏ σ ∈ Finset.univ.erase (1 : G), (ϖ - σ • ϖ) := by
  rw [aeval_def, ← eval_map, ← derivative_map, minpoly_map_eq_charpoly hst,
    MulSemiringAction.charpoly_eq, derivative_prod_finset, eval_finsetSum,
    Finset.sum_eq_single (1 : G)]
  · simp [eval_prod]
  · intro σ _ hσ
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := 1)
      (Finset.mem_erase.2 ⟨Ne.symm hσ, Finset.mem_univ _⟩) (by simp), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

include hst in
/-- `ϖ` generates the fraction field extension. -/
theorem adjoin_eq_top :
    Algebra.adjoin (FractionRing A) {algebraMap S (FractionRing S) ϖ} = ⊤ := by
  have hint : IsIntegral A ϖ := Algebra.IsIntegral.isIntegral ϖ
  set x := algebraMap S (FractionRing S) ϖ
  have hxA : IsIntegral A x := hint.map (IsScalarTower.toAlgHom A S (FractionRing S))
  have hxK : IsIntegral (FractionRing A) x := hxA.tower_top
  have hmin : minpoly (FractionRing A) x = (minpoly A ϖ).map (algebraMap A (FractionRing A)) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing A) hxA,
      minpoly.algebraMap_eq (IsFractionRing.injective S (FractionRing S))]
  have hdeg : Module.finrank (FractionRing A) (FractionRing A)⟮x⟯ = Fintype.card G := by
    rw [IntermediateField.adjoin.finrank hxK, hmin, (minpoly.monic hint).natDegree_map,
      natDegree_minpoly hst]
  have hfin : Module.finrank (FractionRing A) (FractionRing S) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, IsGaloisGroup.card_eq_finrank' G A S,
      IsFractionRing.finrank_eq A (FractionRing A) S (FractionRing S)]
  have : FiniteDimensional (FractionRing A) (FractionRing S) := .of_isLocalization A S A⁰
  have htop : (FractionRing A)⟮x⟯ = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hdeg, IntermediateField.finrank_top', hfin])
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxK.isAlgebraic, htop,
    IntermediateField.top_toSubalgebra]

end Min

end RamanujanPetersson.GOS

end Inline_GOS_A_Min

section Inline_GOS_A_Tot


/-!
# S4-GOS-A, part 4: Hilbert's different formula in the totally ramified case

`S / A` finite torsion-free extension of Dedekind domains with Galois group `G`, `Q` a height-one prime of `S` with
finite residue field and inertia group all of `G`. For a uniformizer `ϖ` of `Q`, the conductor of `A[ϖ]` is prime
to `Q` (part 2), `ϖ` has trivial stabilizer and generates `Frac S` (part 3), so Mathlib's
`conductor_mul_differentIdeal` gives `v_Q(𝔇_{S/A}) = v_Q(f'(ϖ)) = ∑_{σ ≠ 1} v_Q(ϖ - σ ϖ)`
(`ordI_differentIdeal_of_totally`).
-/



open IsDedekindDomain Polynomial
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Tot

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S] [IsGaloisGroup G A S]

variable (A S) in
theorem isSeparable_frac (H : Type*) [Group H] [Finite H] [MulSemiringAction H S]
    [IsGaloisGroup H A S] : Algebra.IsSeparable (FractionRing A) (FractionRing S) := by
  let := IsFractionRing.mulSemiringAction H S (FractionRing S)
  have := IsGaloisGroup.isGalois H (FractionRing A) (FractionRing S)
  infer_instance

omit [IsDedekindDomain A] [Module.Finite A S] [Module.IsTorsionFree A S] [Fintype G] in
/-- An element of `G` fixing `ϖ` fixes `A[ϖ]`, hence (through a nonzero conductor element) all of `S`. -/
theorem eq_one_of_smul_eq {ϖ t : S} (ht : t ∈ conductor A ϖ) (ht0 : t ≠ 0) (σ : G)
    (hσ : σ • ϖ = ϖ) : σ = 1 := by
  have := IsGaloisGroup.commutes (G := G) (A := A) (B := S)
  have hfix : ∀ y ∈ Algebra.adjoin A {ϖ}, σ • y = y := by
    intro y hy
    have hle : Algebra.adjoin A {ϖ} ≤
        AlgHom.equalizer (MulSemiringAction.toAlgHom A S σ) (AlgHom.id A S) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 (by simpa [AlgHom.mem_equalizer] using hσ))
    simpa [AlgHom.mem_equalizer] using hle hy
  have := IsGaloisGroup.faithful (G := G) (A := A) (B := S)
  apply eq_of_smul_eq_smul (α := S)
  intro b
  rw [one_smul]
  have h1 := hfix _ (mem_conductor_iff.1 ht b)
  have h2 := hfix _ (mem_conductor_iff.1 ht 1)
  rw [mul_one] at h2
  rw [smul_mul', h2] at h1
  exact mul_left_cancel₀ ht0 h1

variable (Q : HeightOneSpectrum S) (hI : ∀ σ : G, σ ∈ Q.asIdeal.inertia G)

include hI in
/-- **Hilbert's different formula, totally ramified case**: for a uniformizer `ϖ` of `Q`,
`v_Q(𝔇_{S/A}) = ∑_{σ ≠ 1} v_Q(ϖ - σ ϖ)`. -/
theorem ordI_differentIdeal_of_totally [Finite (S ⧸ Q.asIdeal)] {ϖ : S} (h1 : ϖ ∈ Q.asIdeal)
    (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    ordI Q (differentIdeal A S) =
      ∑ σ ∈ Finset.univ.erase (1 : G), ordI Q (Ideal.span {ϖ - σ • ϖ}) := by
  obtain ⟨t, ht, htQ⟩ := exists_mem_conductor_not_mem (A := A) Q hI h1 h2
  have ht0 : t ≠ 0 := fun h => htQ (h ▸ Q.asIdeal.zero_mem)
  have hst : ∀ σ : G, σ • ϖ = ϖ → σ = 1 := fun σ hσ => eq_one_of_smul_eq ht ht0 σ hσ
  have := isSeparable_frac A S G
  have : FiniteDimensional (FractionRing A) (FractionRing S) := .of_isLocalization A S A⁰
  have : IsIntegralClosure S A (FractionRing S) :=
    IsIntegralClosure.of_isIntegrallyClosed S A (FractionRing S)
  have hcd := conductor_mul_differentIdeal A (FractionRing A) (FractionRing S) ϖ (adjoin_eq_top hst)
  rw [aeval_derivative_minpoly hst] at hcd
  have hne : ∀ σ ∈ Finset.univ.erase (1 : G), ϖ - σ • ϖ ≠ 0 := by
    intro σ hσ h
    exact (Finset.mem_erase.1 hσ).1 (hst σ (sub_eq_zero.1 h).symm)
  have hc0 : conductor A ϖ ≠ ⊥ := fun h => ht0 (Ideal.mem_bot.1 (h ▸ ht))
  rw [← ordI_span_prod Q _ _ hne, ← hcd, ordI_mul Q hc0 (differentIdeal_ne_bot (A := A) (B := S)),
    (ordI_eq_zero_iff Q hc0).2 (fun h => htQ (h ht)), zero_add]

end Tot

end RamanujanPetersson.GOS

end Inline_GOS_A_Tot

section Inline_GOS_A_Unr


/-!
# S4-GOS-A, part 5: the inertia ring is unramified

For `S / R` Dedekind with Galois group `G` and `Q` a height-one prime of `S` with finite residue field, the inertia
ring `S ^ (I_Q)` (`inertiaRing R G Q`) is Dedekind and finite over `R` (global instances `fixed_*`), the prime
`Q ∩ S^(I_Q)` has ramification index one over `R` (`ramificationIdx_inertiaRing`), so `Q` does not divide the
extended different of `S^(I_Q) / R` (`not_dvd_map_differentIdeal`).
-/



open IsDedekindDomain
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Instances

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S] (H : Subgroup G) [Module.Finite R S]

instance fixed_finite_top : Module.Finite (FixedPoints.subalgebra R S H) S := Swan.finite_fixed H

instance fixed_isIntegral : Algebra.IsIntegral R (FixedPoints.subalgebra R S H) :=
  Swan.isIntegral_fixedSubalgebra H

variable [IsDedekindDomain R] [IsDedekindDomain S]

instance fixed_isDedekindDomain : IsDedekindDomain (FixedPoints.subalgebra R S H) :=
  Swan.isDedekindDomain_fixed H

instance fixed_finite_bot : Module.Finite R (FixedPoints.subalgebra R S H) :=
  have : IsNoetherian R (FixedPoints.subalgebra R S H) :=
    isNoetherian_of_injective (FixedPoints.subalgebra R S H).val.toLinearMap Subtype.val_injective
  Module.IsNoetherian.finite R _

end Instances

section Unr

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

variable (R G) in
/-- The inertia ring `S ^ (I_Q)`. -/
abbrev inertiaRing : Subalgebra R S := FixedPoints.subalgebra R S (Q.asIdeal.inertia G)

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [Module.IsTorsionFree R S] in
attribute [local instance] Ideal.Quotient.field in
theorem finite_residueField {T : Type*} [CommRing T] [Algebra T S] (p : Ideal T) [p.IsMaximal]
    [Q.asIdeal.LiesOver p] : Finite p.ResidueField := by
  have : Finite (T ⧸ p) :=
    Finite.of_injective (algebraMap (T ⧸ p) (S ⧸ Q.asIdeal)) (RingHom.injective _)
  exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField p).2

/-- The prime `Q ∩ S^(I_Q)` has ramification index `1` over `R`. -/
theorem ramificationIdx_inertiaRing :
    (Q.asIdeal.under (inertiaRing R G Q)).ramificationIdx R = 1 := by
  have := Q.isMaximal
  have hQ : Q.asIdeal.LiesOver (Q.asIdeal.under (inertiaRing R G Q)) := ⟨rfl⟩
  have hQR : Q.asIdeal.LiesOver (Q.asIdeal.under R) := ⟨rfl⟩
  have : (Q.asIdeal.under R).IsMaximal := Ideal.IsMaximal.under R Q.asIdeal
  have : (Q.asIdeal.under (inertiaRing R G Q)).IsMaximal :=
    Ideal.IsMaximal.under (inertiaRing R G Q) Q.asIdeal
  have := finite_residueField Q (Q.asIdeal.under R)
  have := finite_residueField Q (Q.asIdeal.under (inertiaRing R G Q))
  have h1 : Q.asIdeal.ramificationIdx R = Nat.card (Q.asIdeal.inertia G) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.asIdeal.under R) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.asIdeal.under R) Q.asIdeal G]
  have htop : Q.asIdeal.inertia (Q.asIdeal.inertia G) = ⊤ :=
    eq_top_iff.2 fun σ _ => AddSubgroup.coe_mem_inertia.1 σ.2
  have h2 : Q.asIdeal.ramificationIdx (inertiaRing R G Q) = Nat.card (Q.asIdeal.inertia G) := by
    rw [← Subgroup.card_top (G := Q.asIdeal.inertia G), ← htop,
      Ideal.card_inertia_eq_ramificationIdxIn (G := Q.asIdeal.inertia G)
        (Q.asIdeal.under (inertiaRing R G Q)) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.asIdeal.under (inertiaRing R G Q)) Q.asIdeal
        (Q.asIdeal.inertia G)]
  have h3 := Ideal.ramificationIdx_tower (R := R) (Q.asIdeal.under (inertiaRing R G Q)) Q.asIdeal
  rw [h1, h2] at h3
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [one_mul]; exact h3.symm)

/-- The inertia ring is unramified at `Q ∩ S^(I_Q)`, so `Q` does not divide the extended different of
`S^(I_Q) / R`. -/
theorem not_dvd_map_differentIdeal :
    ¬ Q.asIdeal ∣ (differentIdeal R (inertiaRing R G Q)).map (algebraMap (inertiaRing R G Q) S) := by
  have := Q.isMaximal
  have := isSeparable_frac R S G
  have : Algebra.IsSeparable (FractionRing R) (FractionRing (inertiaRing R G Q)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ _ (FractionRing S)
  have : (Q.asIdeal.under (inertiaRing R G Q)).IsMaximal :=
    Ideal.IsMaximal.under (inertiaRing R G Q) Q.asIdeal
  have : ((Q.asIdeal.under (inertiaRing R G Q)).under R).IsMaximal :=
    Ideal.IsMaximal.under R _
  have : Q.asIdeal.LiesOver ((Q.asIdeal.under (inertiaRing R G Q)).under R) := ⟨rfl⟩
  have := finite_residueField Q ((Q.asIdeal.under (inertiaRing R G Q)).under R)
  have hq : Algebra.IsUnramifiedAt R (Q.asIdeal.under (inertiaRing R G Q)) :=
    Ideal.ramificationIdx_eq_one_iff.1 (ramificationIdx_inertiaRing Q)
  have hnd := (not_dvd_differentIdeal_iff (A := R) (B := inertiaRing R G Q)).2 hq
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  rwa [Ideal.dvd_iff_le] at hnd

end Unr

end RamanujanPetersson.GOS

end Inline_GOS_A_Unr

section Inline_GOS_A_Hilb


/-!
# S4-GOS-A, part 6: Hilbert's different formula

`S / R` finite torsion-free extension of Dedekind domains with Galois group `G`, `Q` a height-one prime of `S` with
finite residue field and inertia group `I_Q`. The different of `S / R` has the same `Q`-exponent as that of
`S / S^(I_Q)` (part 5: `S^(I_Q)` is unramified at `Q`), and `S / S^(I_Q)` is totally ramified (part 4), so
* `ordI_differentIdeal`: `v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} v_Q(ϖ - σ ϖ)` for any uniformizer `ϖ`;
* `ordI_differentIdeal_eq_sum_ramFn`: `v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} i_Q(σ)` with S4-Swan's ramification
  function of `Swan.inertiaLocData`;
* `ordI_differentIdeal_eq_sum_lower`: `v_Q(𝔇_{S/R}) = ∑_{u ≥ 0} (|G_u| - 1)` (lower numbering).
The subgroup version (`S^H ⊆ S`) is the case `R := FixedPoints.subalgebra R S H`, `G := H` (instances of part 5).
-/



open IsDedekindDomain
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Hilb

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)] [Fintype (Q.asIdeal.inertia G)]

omit [Fintype (Q.asIdeal.inertia G)] in
/-- `𝔇_{S/R}` and `𝔇_{S/S^(I_Q)}` have the same `Q`-exponent. -/
theorem ordI_differentIdeal_eq_inertiaRing :
    ordI Q (differentIdeal R S) = ordI Q (differentIdeal (inertiaRing R G Q) S) := by
  have := isSeparable_frac R S G
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal R (inertiaRing R G Q) S
  have hne : differentIdeal R S ≠ ⊥ := differentIdeal_ne_bot
  rw [h] at hne ⊢
  have hne' := hne
  rw [Ne, Ideal.mul_eq_bot, not_or] at hne'
  have h0 : ordI Q ((differentIdeal R (inertiaRing R G Q)).map
      (algebraMap (inertiaRing R G Q) S)) = 0 :=
    (ordI_eq_zero_iff Q hne'.2).2 fun hle =>
      not_dvd_map_differentIdeal (R := R) (G := G) Q (Ideal.dvd_iff_le.2 hle)
  rw [ordI_mul Q hne'.1 hne'.2, h0, add_zero]

/-- **Hilbert's different formula**: for a uniformizer `ϖ` of `Q`,
`v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} v_Q(ϖ - σ ϖ)`. -/
theorem ordI_differentIdeal {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    ordI Q (differentIdeal R S) = ∑ σ ∈ Finset.univ.erase (1 : Q.asIdeal.inertia G),
      ordI Q (Ideal.span {ϖ - (σ : G) • ϖ}) := by
  rw [ordI_differentIdeal_eq_inertiaRing (G := G) Q, ordI_differentIdeal_of_totally
    (A := inertiaRing R G Q) (G := Q.asIdeal.inertia G) Q
    (fun σ => AddSubgroup.coe_mem_inertia.1 σ.2) h1 h2]
  exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl

end Hilb

end RamanujanPetersson.GOS

end Inline_GOS_A_Hilb

end

theorem solution
    {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (Q : IsDedekindDomain.HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]
    {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    (Associates.mk Q.asIdeal).count (Associates.mk (differentIdeal R S)).factors =
      ∑ᶠ σ ∈ (Q.asIdeal.inertia G : Set G) \ {1},
        (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {ϖ - σ • ϖ})).factors := by
  classical
  letI : Fintype (Q.asIdeal.inertia G) := Fintype.ofFinite _
  have h := RamanujanPetersson.GOS.ordI_differentIdeal (R := R) (G := G) Q h1 h2
  unfold RamanujanPetersson.GOS.ordI at h
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
  convert h using 1
  symm
  refine Finset.sum_bij (fun σ _ => (σ : G)) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
    exact ⟨σ.2, fun h => (Finset.ne_of_mem_erase hσ) (Subtype.ext h)⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact ⟨⟨x, hx.1⟩, Finset.mem_erase.2 ⟨fun h => hx.2 (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
  · intro σ _
    rfl
