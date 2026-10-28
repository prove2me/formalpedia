-- Prove2me | solution 1 for NoetherianScheme.exists_valuationRing_noetherianSpace_not_isNoetherianScheme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:49:07.150531+00:00
-- url     : https://prove2.me/submissions/afc15ec7-d6df-41f9-9de5-a3615b58f455

import Mathlib
import Definitions.Def_NoetherianScheme_defs

open AlgebraicGeometry

namespace S216NS

abbrev K := HahnSeries ℚ ℚ

lemma ot_mul (x y : K) : (x * y).orderTop = x.orderTop + y.orderTop := HahnSeries.orderTop_mul x y

lemma ot_coe {x : K} (hx : x ≠ 0) : ∃ a : ℚ, x.orderTop = a :=
  WithTop.ne_top_iff_exists.mp (by simpa [HahnSeries.orderTop_eq_top] using hx) |>.imp fun _ h => h.symm

lemma ot_inv {x : K} (hx : x ≠ 0) (a : ℚ) (ha : x.orderTop = a) : x⁻¹.orderTop = ((-a : ℚ) : WithTop ℚ) := by
  obtain ⟨b, hb⟩ := ot_coe (inv_ne_zero hx)
  have h := ot_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, HahnSeries.orderTop_one, ha, hb, ← WithTop.coe_add] at h
  have : a + b = 0 := by exact_mod_cast h.symm
  rw [hb]; congr 1; linarith

def R : Subring K where
  carrier := {x | 0 ≤ x.orderTop}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, ot_mul] at *; exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

lemma dvd_of_le {a b : R} (ha : (a : K) ≠ 0) (h : (a : K).orderTop ≤ (b : K).orderTop) :
    ∃ c : R, a * c = b := by
  obtain ⟨p, hp⟩ := ot_coe ha
  refine ⟨⟨(b : K) * (a : K)⁻¹, ?_⟩, ?_⟩
  · show 0 ≤ ((b : K) * (a : K)⁻¹).orderTop
    rw [ot_mul, ot_inv ha p hp]
    by_cases hb : (b : K) = 0
    · simp [hb]
    obtain ⟨q, hq⟩ := ot_coe hb
    rw [hq, ← WithTop.coe_add]; rw [hp, hq] at h
    have : p ≤ q := by exact_mod_cast h
    exact_mod_cast (by linarith : (0:ℚ) ≤ q + -p)
  · apply Subtype.ext; show (a : K) * ((b : K) * (a : K)⁻¹) = b
    field_simp

instance : ValuationRing R where
  cond' a b := by
    by_cases ha : (a : K) = 0
    · refine ⟨0, Or.inr ?_⟩
      have : a = 0 := Subtype.ext ha
      simp [this]
    by_cases hb : (b : K) = 0
    · refine ⟨0, Or.inl ?_⟩
      have : b = 0 := Subtype.ext hb
      simp [this]
    rcases le_total (a : K).orderTop (b : K).orderTop with h | h
    · obtain ⟨c, hc⟩ := dvd_of_le ha h; exact ⟨c, Or.inl hc⟩
    · obtain ⟨c, hc⟩ := dvd_of_le hb h; exact ⟨c, Or.inr hc⟩

lemma isUnit_iff (y : R) : IsUnit y ↔ (y : K).orderTop = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h := ot_mul (u : R) ((u⁻¹ : Rˣ) : R)
    have h1 : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [h1, HahnSeries.orderTop_one] at h
    have p1 : (0 : WithTop ℚ) ≤ ((u : R) : K).orderTop := (u : R).2
    have p2 : (0 : WithTop ℚ) ≤ (((u⁻¹ : Rˣ) : R) : K).orderTop := ((u⁻¹ : Rˣ) : R).2
    have hne : ((u : R) : K) ≠ 0 := fun h0 => by simp [h0] at h1
    have hne2 : (((u⁻¹ : Rˣ) : R) : K) ≠ 0 := fun h0 => by simp [h0] at h1
    obtain ⟨a, ha⟩ := ot_coe hne; obtain ⟨b, hb⟩ := ot_coe hne2
    rw [ha, hb, ← WithTop.coe_add] at h
    rw [ha] at p1 ⊢; rw [hb] at p2
    have : a + b = 0 := by exact_mod_cast h.symm
    have : (0:ℚ) ≤ a := by exact_mod_cast p1
    have : (0:ℚ) ≤ b := by exact_mod_cast p2
    exact_mod_cast (by linarith : a = 0)
  · intro h
    have hne : (y : K) ≠ 0 := fun h0 => by simp [h0] at h
    refine isUnit_iff_exists_inv.mpr ⟨⟨(y : K)⁻¹, ?_⟩, ?_⟩
    · show 0 ≤ (y : K)⁻¹.orderTop
      rw [ot_inv hne 0 h]; simp
    · apply Subtype.ext; show (y : K) * (y : K)⁻¹ = 1; field_simp

lemma pos_of_nonunit {y : R} (hy : ¬ IsUnit y) (h0 : (y : K) ≠ 0) :
    ∃ r : ℚ, 0 < r ∧ (y : K).orderTop = r := by
  obtain ⟨r, hr⟩ := ot_coe h0
  refine ⟨r, ?_, hr⟩
  have p := y.2; change (0 : WithTop ℚ) ≤ (y : K).orderTop at p
  rw [hr] at p
  have : (0:ℚ) ≤ r := by exact_mod_cast p
  rcases this.lt_or_eq with h | h
  · exact h
  · exact absurd ((isUnit_iff y).2 (by rw [hr, ← h]; rfl)) hy

lemma ot_pow (y : K) (n : ℕ) : (y ^ n).orderTop = n • y.orderTop := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ot_mul, ih, succ_nsmul]

lemma prime_eq (P : Ideal R) [hP : P.IsPrime] (hne : P ≠ ⊥) (y : R) : y ∈ P ↔ ¬ IsUnit y := by
  constructor
  · intro hy hu; exact hP.ne_top (P.eq_top_of_isUnit_mem hy hu)
  intro hy
  by_cases hy0 : (y : K) = 0
  · have : y = 0 := Subtype.ext hy0
    rw [this]; exact P.zero_mem
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxK : (x : K) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨q, hq⟩ := ot_coe hxK
  obtain ⟨r, hr0, hr⟩ := pos_of_nonunit hy hy0
  obtain ⟨n, hn⟩ := exists_nat_ge (q / r)
  have hle : (x : K).orderTop ≤ ((y ^ n : R) : K).orderTop := by
    rw [Subring.coe_pow, ot_pow, hr, hq, ← WithTop.coe_nsmul]
    have : q ≤ n • r := by
      rw [nsmul_eq_mul]; rwa [div_le_iff₀ hr0] at hn
    exact_mod_cast this
  obtain ⟨c, hc⟩ := dvd_of_le hxK hle
  have : y ^ n ∈ P := hc ▸ P.mul_mem_right c hxP
  exact hP.mem_of_pow_mem n this

instance : Finite (PrimeSpectrum R) := by
  classical
  refine Finite.of_injective (fun p : PrimeSpectrum R => decide (p.asIdeal = ⊥)) ?_
  intro p q h
  simp only at h
  by_cases hp : p.asIdeal = ⊥
  · have hq : q.asIdeal = ⊥ := by simpa [hp] using h.symm
    ext1; rw [hp, hq]
  · have hq : q.asIdeal ≠ ⊥ := by simpa [hp] using h.symm
    ext1; ext y
    rw [@prime_eq p.asIdeal p.2 hp, @prime_eq q.asIdeal q.2 hq]

lemma not_noeth : ¬ IsNoetherianRing R := by
  intro hN
  have : IsPrincipalIdealRing R := inferInstance
  obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal R)).principal
  have hmem : ∀ y : R, y ∈ IsLocalRing.maximalIdeal R ↔ ¬ IsUnit y := fun y => IsLocalRing.mem_maximalIdeal y
  -- t = single 1 1 is a nonunit
  let t : R := ⟨HahnSeries.single (1:ℚ) (1:ℚ), by
    show (0 : WithTop ℚ) ≤ _; rw [HahnSeries.orderTop_single one_ne_zero]; exact_mod_cast zero_le_one⟩
  have ht : ¬ IsUnit t := by
    rw [isUnit_iff]; show (HahnSeries.single (1:ℚ) (1:ℚ)).orderTop ≠ 0
    rw [HahnSeries.orderTop_single one_ne_zero]; simp
  have htm : t ∈ IsLocalRing.maximalIdeal R := (hmem t).2 ht
  have hx0 : (x : K) ≠ 0 := by
    intro h0
    have : x = 0 := Subtype.ext h0
    rw [hx, this, Submodule.span_singleton_eq_bot.mpr rfl] at htm
    have : t = 0 := htm
    have h' : ((t : R) : K) = 0 := by rw [this]; rfl
    simp [t] at h'
  have hxm : x ∈ IsLocalRing.maximalIdeal R := by rw [hx]; exact Submodule.mem_span_singleton_self x
  obtain ⟨q, hq0, hq⟩ := pos_of_nonunit ((hmem x).1 hxm) hx0
  let z : R := ⟨HahnSeries.single (q/2) (1:ℚ), by
    show (0 : WithTop ℚ) ≤ _; rw [HahnSeries.orderTop_single one_ne_zero]
    exact_mod_cast (by linarith : (0:ℚ) ≤ q/2)⟩
  have hz : ¬ IsUnit z := by
    rw [isUnit_iff]; show (HahnSeries.single (q/2) (1:ℚ)).orderTop ≠ 0
    rw [HahnSeries.orderTop_single one_ne_zero]
    exact_mod_cast (by linarith : q/2 ≠ 0)
  have hzm := (hmem z).2 hz
  rw [hx, Submodule.mem_span_singleton] at hzm
  obtain ⟨c, hc⟩ := hzm
  have hcK : (c : K) * (x : K) = HahnSeries.single (q/2) (1:ℚ) := congrArg Subtype.val hc
  have h1 := ot_mul (c : K) (x : K)
  rw [hcK, HahnSeries.orderTop_single one_ne_zero, hq] at h1
  have pc : (0 : WithTop ℚ) ≤ (c : K).orderTop := c.2
  by_cases hc0 : (c : K) = 0
  · rw [hc0, HahnSeries.orderTop_zero] at h1; simp at h1
  obtain ⟨s, hs⟩ := ot_coe hc0
  rw [hs] at h1 pc; rw [← WithTop.coe_add] at h1
  have e : q/2 = s + q := by exact_mod_cast h1
  have : (0:ℚ) ≤ s := by exact_mod_cast pc
  linarith

end S216NS

open S216NS in
theorem solution :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R), ValuationRing R ∧ ¬ IsNoetherianRing R ∧
      TopologicalSpace.NoetherianSpace (Spec (CommRingCat.of R)) ∧
      ¬ NoetherianScheme.IsNoetherianScheme (Spec (CommRingCat.of R)) := by
  refine ⟨S216NS.R, inferInstance, inferInstance, inferInstance, not_noeth, ?_, ?_⟩
  · exact @TopologicalSpace.Finite.to_noetherianSpace (PrimeSpectrum S216NS.R) _ inferInstance
  · rintro ⟨s, hs, hcov⟩
    let S : s → (Spec (CommRingCat.of S216NS.R)).affineOpens := fun i => ⟨i.1, (hs i.1 i.2).1⟩
    have hS : (⨆ i, (S i : (Spec (CommRingCat.of S216NS.R)).Opens)) = ⊤ := by
      rw [eq_top_iff]; intro x _
      obtain ⟨U, hU, hx⟩ := hcov x
      exact (TopologicalSpace.Opens.mem_iSup).2 ⟨⟨U, hU⟩, hx⟩
    have hN : IsNoetherian (Spec (CommRingCat.of S216NS.R)) :=
      (isNoetherian_iff_of_finite_iSup_eq_top hS).2 fun i => (hs i.1 i.2).2
    exact not_noeth (isNoetherian_Spec.mp hN)
