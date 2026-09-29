-- Prove2me | solution 1 for ModularCurve.exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c50a355c-b3c5-528c-8a52-494a44e7d786

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing

namespace G4Gauss

section DVR

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma map_residue_eq_zero_iff (z : PowerSeries R) :
    PowerSeries.map (IsLocalRing.residue R) z = 0 ↔
      ∀ n, PowerSeries.coeff n z ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro h n
    have h1 := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    ext n
    rw [PowerSeries.coeff_map, map_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)

lemma exists_eq_C_mul {ϖ : R} (hϖ : Irreducible ϖ) (z : PowerSeries R)
    (hz : PowerSeries.map (IsLocalRing.residue R) z = 0) :
    ∃ z' : PowerSeries R, z = PowerSeries.C ϖ * z' := by
  have h := (map_residue_eq_zero_iff z).mp hz
  have h' : ∀ n, ∃ c, PowerSeries.coeff n z = ϖ * c := fun n => by
    have h1 := h n
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  choose c hc using h'
  exact ⟨PowerSeries.mk c, by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]⟩

lemma factor_aux {ϖ : R} (hϖ : Irreducible ϖ) :
    ∀ (N : ℕ) (z : PowerSeries R) (n₀ : ℕ), ¬ ϖ ^ (N + 1) ∣ PowerSeries.coeff n₀ z →
      ∃ (a : ℕ) (z' : PowerSeries R), z = PowerSeries.C ϖ ^ a * z' ∧
        PowerSeries.map (IsLocalRing.residue R) z' ≠ 0 := by
  intro N
  induction N with
  | zero =>
    intro z n₀ hn
    refine ⟨0, z, by rw [pow_zero, one_mul], ?_⟩
    intro hz
    apply hn
    have h1 := (map_residue_eq_zero_iff z).mp hz n₀
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    rwa [zero_add, pow_one]
  | succ N ih =>
    intro z n₀ hn
    by_cases hz : PowerSeries.map (IsLocalRing.residue R) z = 0
    · obtain ⟨z₁, hz₁⟩ := exists_eq_C_mul hϖ z hz
      have hn' : ¬ ϖ ^ (N + 1) ∣ PowerSeries.coeff n₀ z₁ := by
        intro hd
        apply hn
        rw [hz₁, PowerSeries.coeff_C_mul, pow_succ']
        exact mul_dvd_mul_left ϖ hd
      obtain ⟨a, z', h1, h2⟩ := ih z₁ n₀ hn'
      refine ⟨a + 1, z', ?_, h2⟩
      rw [hz₁, h1, pow_succ', mul_assoc]
    · exact ⟨0, z, by rw [pow_zero, one_mul], hz⟩

lemma factor {ϖ : R} (hϖ : Irreducible ϖ) (z : PowerSeries R) (hz : z ≠ 0) :
    ∃ (a : ℕ) (z' : PowerSeries R), z = PowerSeries.C ϖ ^ a * z' ∧
      PowerSeries.map (IsLocalRing.residue R) z' ≠ 0 := by
  have hex : ∃ n₀, PowerSeries.coeff n₀ z ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (PowerSeries.ext (fun n => by rw [h n, map_zero]))
  obtain ⟨n₀, hn₀⟩ := hex
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn₀ hϖ
  apply factor_aux hϖ m z n₀
  intro hd
  rw [hu, pow_succ, mul_comm (↑u : R)] at hd
  have hϖ0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hdu : ϖ ∣ ↑u := (mul_dvd_mul_iff_left hϖ0).mp hd
  exact hϖ.not_isUnit (isUnit_of_dvd_unit hdu u.isUnit)

end DVR

section Main

variable {L : Type} [Field L] (A₀ : ValuationSubring L)

noncomputable def φ : PowerSeries ↥A₀ →+* LaurentSeries L :=
  (HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap ↥A₀ L))

lemma φ_apply (x : PowerSeries ↥A₀) :
    φ A₀ x = HahnSeries.ofPowerSeries ℤ L (PowerSeries.map (algebraMap ↥A₀ L) x) := rfl

lemma φ_injective : Function.Injective (φ A₀) := by
  intro x y h
  rw [φ_apply, φ_apply] at h
  have h' : PowerSeries.map (algebraMap ↥A₀ L) x = PowerSeries.map (algebraMap ↥A₀ L) y :=
    HahnSeries.ofPowerSeries_injective h
  refine PowerSeries.ext (fun n => ?_)
  apply FaithfulSMul.algebraMap_injective ↥A₀ L
  have h1 := congrArg (PowerSeries.coeff n) h'
  rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at h1

lemma φ_ne_zero {x : PowerSeries ↥A₀} (hx : x ≠ 0) : φ A₀ x ≠ 0 :=
  (map_ne_zero_iff _ (φ_injective A₀)).mpr hx

lemma C_pow_ne_zero {ϖ : ↥A₀} (hϖ : ϖ ≠ 0) (a : ℕ) : (PowerSeries.C ϖ) ^ a ≠ 0 :=
  pow_ne_zero _ ((map_ne_zero_iff _ PowerSeries.C_injective).mpr hϖ)

noncomputable def L₂ : Subfield (LaurentSeries L) where
  carrier := {f | ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧ f * φ A₀ y = φ A₀ x}
  mul_mem' := by
    rintro f g ⟨x, y, hy, hf⟩ ⟨x', y', hy', hg⟩
    refine ⟨x * x', y * y', mul_ne_zero hy hy', ?_⟩
    rw [map_mul, map_mul]
    linear_combination (g * φ A₀ y') * hf + (φ A₀ x) * hg
  one_mem' := ⟨1, 1, one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨x, y, hy, hf⟩ ⟨x', y', hy', hg⟩
    refine ⟨x * y' + x' * y, y * y', mul_ne_zero hy hy', ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    linear_combination (φ A₀ y') * hf + (φ A₀ y) * hg
  zero_mem' := ⟨0, 1, one_ne_zero, by rw [map_zero, zero_mul]⟩
  neg_mem' := by
    rintro f ⟨x, y, hy, hf⟩
    refine ⟨-x, y, hy, ?_⟩
    rw [map_neg, neg_mul, hf]
  inv_mem' := by
    rintro f ⟨x, y, hy, hf⟩
    by_cases hf0 : f = 0
    · exact ⟨0, 1, one_ne_zero, by rw [hf0, inv_zero, map_zero, zero_mul]⟩
    · have hx : x ≠ 0 := by
        rintro rfl
        rw [map_zero] at hf
        exact (mul_ne_zero hf0 (φ_ne_zero A₀ hy)) hf
      refine ⟨y, x, hx, ?_⟩
      rw [← hf, inv_mul_cancel_left₀ hf0]

noncomputable def W₂' : Subring (LaurentSeries L) where
  carrier := {f | ∃ x y : PowerSeries ↥A₀, PowerSeries.map (IsLocalRing.residue ↥A₀) y ≠ 0 ∧
    f * φ A₀ y = φ A₀ x}
  mul_mem' := by
    rintro f g ⟨x, y, hy, hf⟩ ⟨x', y', hy', hg⟩
    refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
    rw [map_mul, map_mul]
    linear_combination (g * φ A₀ y') * hf + (φ A₀ x) * hg
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨x, y, hy, hf⟩ ⟨x', y', hy', hg⟩
    refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    linear_combination (φ A₀ y') * hf + (φ A₀ y) * hg
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_zero, zero_mul]⟩
  neg_mem' := by
    rintro f ⟨x, y, hy, hf⟩
    refine ⟨-x, y, hy, ?_⟩
    rw [map_neg, neg_mul, hf]

lemma mem_or_inv_mem (hdvr : IsDiscreteValuationRing ↥A₀) (f : LaurentSeries L)
    (hf : f ∈ L₂ A₀) : f ∈ W₂' A₀ ∨ f⁻¹ ∈ W₂' A₀ := by
  haveI := hdvr
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A₀
  by_cases hx : x = 0
  · left
    have hf0 : f = 0 := by
      rw [hx, map_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (φ_ne_zero A₀ hy)
    exact ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [hf0, map_zero, zero_mul]⟩
  · obtain ⟨a, x', hxe, hx'⟩ := factor hϖ x hx
    obtain ⟨b, y', hye, hy'⟩ := factor hϖ y hy
    rcases le_or_gt b a with hba | hab
    · left
      refine ⟨PowerSeries.C ϖ ^ (a - b) * x', y', hy', ?_⟩
      have hne : φ A₀ (PowerSeries.C ϖ ^ b) ≠ 0 := φ_ne_zero A₀ (C_pow_ne_zero A₀ hϖ.ne_zero b)
      apply mul_left_cancel₀ hne
      have eq1 : φ A₀ (PowerSeries.C ϖ ^ b) * (f * φ A₀ y') = f * φ A₀ y := by
        rw [hye, map_mul]; ring
      have eq2 : φ A₀ (PowerSeries.C ϖ ^ b) * φ A₀ (PowerSeries.C ϖ ^ (a - b) * x') = φ A₀ x := by
        rw [hxe, ← map_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hba]
      rw [eq1, eq2, h]
    · right
      have hf0 : f ≠ 0 := by
        have hφx : φ A₀ x ≠ 0 := φ_ne_zero A₀ hx
        rw [← h] at hφx
        exact left_ne_zero_of_mul hφx
      refine ⟨PowerSeries.C ϖ ^ (b - a) * y', x', hx', ?_⟩
      have eq0 : φ A₀ y = f⁻¹ * φ A₀ x := by
        rw [← h, inv_mul_cancel_left₀ hf0]
      have hne : φ A₀ (PowerSeries.C ϖ ^ a) ≠ 0 := φ_ne_zero A₀ (C_pow_ne_zero A₀ hϖ.ne_zero a)
      apply mul_left_cancel₀ hne
      have eq1 : φ A₀ (PowerSeries.C ϖ ^ a) * (f⁻¹ * φ A₀ x') = f⁻¹ * φ A₀ x := by
        rw [hxe, map_mul]; ring
      have eq2 : φ A₀ (PowerSeries.C ϖ ^ a) * φ A₀ (PowerSeries.C ϖ ^ (b - a) * y') = φ A₀ y := by
        rw [hye, ← map_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
      rw [eq1, eq2, eq0]

noncomputable def W₂ (hdvr : IsDiscreteValuationRing ↥A₀) : ValuationSubring ↥(L₂ A₀) where
  toSubring := (W₂' A₀).comap (L₂ A₀).subtype
  mem_or_inv_mem' := by
    intro f
    rcases mem_or_inv_mem A₀ hdvr (f : LaurentSeries L) f.2 with h | h
    · exact Or.inl h
    · right
      show (L₂ A₀).subtype f⁻¹ ∈ W₂' A₀
      rw [map_inv₀]
      exact h

lemma mem_W₂_iff (hdvr : IsDiscreteValuationRing ↥A₀) (f : ↥(L₂ A₀)) :
    f ∈ W₂ A₀ hdvr ↔ ∃ x y : PowerSeries ↥A₀, PowerSeries.map (IsLocalRing.residue ↥A₀) y ≠ 0 ∧
      (f : LaurentSeries L) * φ A₀ y = φ A₀ x := Iff.rfl

private lemma _root_.G4Gauss.mem_nonunits_iff (hdvr : IsDiscreteValuationRing ↥A₀) (f : ↥(L₂ A₀)) :
    f ∈ (W₂ A₀ hdvr).nonunits ↔ ∃ x y : PowerSeries ↥A₀,
      PowerSeries.map (IsLocalRing.residue ↥A₀) y ≠ 0 ∧
      PowerSeries.map (IsLocalRing.residue ↥A₀) x = 0 ∧ (f : LaurentSeries L) * φ A₀ y = φ A₀ x := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro hlt
    have hf : f ∈ W₂ A₀ hdvr := (ValuationSubring.valuation_le_one_iff _ _).mp hlt.le
    obtain ⟨x, y, hy, h⟩ := (mem_W₂_iff A₀ hdvr f).mp hf
    by_cases hx : PowerSeries.map (IsLocalRing.residue ↥A₀) x = 0
    · exact ⟨x, y, hy, hx, h⟩
    · exfalso
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx (map_zero _)
      have hf0 : (f : LaurentSeries L) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h
        exact φ_ne_zero A₀ hx0 h.symm
      have hf0' : f ≠ 0 := by
        rintro rfl
        exact hf0 rfl
      have hfinv : f⁻¹ ∈ W₂ A₀ hdvr := (mem_W₂_iff A₀ hdvr f⁻¹).mpr ⟨y, x, hx, by
        rw [Subfield.coe_inv, ← h, inv_mul_cancel_left₀ hf0]⟩
      have hunit : IsUnit (⟨f, hf⟩ : ↥(W₂ A₀ hdvr)) :=
        isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hfinv⟩, Subtype.ext (mul_inv_cancel₀ hf0')⟩
      have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hunit
      have h1' : (W₂ A₀ hdvr).valuation f = 1 := h1
      rw [h1'] at hlt
      exact lt_irrefl _ hlt
  · rintro ⟨x, y, hy, hx, h⟩
    have hf : f ∈ W₂ A₀ hdvr := (mem_W₂_iff A₀ hdvr f).mpr ⟨x, y, hy, h⟩
    rcases ValuationSubring.valuation_lt_one_or_eq_one (W₂ A₀ hdvr) ⟨f, hf⟩ with hlt | h1
    · exact hlt
    · exfalso
      have hunit : IsUnit (⟨f, hf⟩ : ↥(W₂ A₀ hdvr)) :=
        (ValuationSubring.valuation_eq_one_iff _ _).mpr h1
      obtain ⟨g, hg⟩ := hunit.exists_right_inv
      have hg1 : f * (g : ↥(L₂ A₀)) = 1 := congrArg Subtype.val hg
      have hg2 : (f : LaurentSeries L) * ((g : ↥(L₂ A₀)) : LaurentSeries L) = 1 := by
        have h2 := congrArg (fun w : ↥(L₂ A₀) => (w : LaurentSeries L)) hg1
        simpa using h2
      obtain ⟨x', y', hy', h'⟩ := (mem_W₂_iff A₀ hdvr _).mp g.2
      have hyy : y * y' = x * x' := φ_injective A₀ (by
        rw [map_mul, map_mul, ← h, ← h']
        linear_combination (-(φ A₀ y * φ A₀ y')) * hg2)
      have h3 := congrArg (PowerSeries.map (IsLocalRing.residue ↥A₀)) hyy
      rw [map_mul, map_mul, hx, zero_mul] at h3
      exact (mul_ne_zero hy hy') h3

p2m_export "G4Gauss" "mem_nonunits_iff"
end Main

end G4Gauss

open G4Gauss in
theorem solution
    (L : Type) [Field L] (A₀ : ValuationSubring L) (hdvr : IsDiscreteValuationRing ↥A₀) :
    ∃ (L₂ : Subfield (LaurentSeries L)) (W₂ : ValuationSubring ↥L₂),

      (∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
        f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧

      (∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
        ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧

      (∀ f : ↥L₂, f ∈ W₂.nonunits ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
        x.map (IsLocalRing.residue ↥A₀) = 0 ∧
        ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) :=
  ⟨L₂ A₀, W₂ A₀ hdvr, fun _ => Iff.rfl, fun f => mem_W₂_iff A₀ hdvr f, fun f => mem_nonunits_iff A₀ hdvr f⟩

#print axioms solution

end S_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing (solution)
