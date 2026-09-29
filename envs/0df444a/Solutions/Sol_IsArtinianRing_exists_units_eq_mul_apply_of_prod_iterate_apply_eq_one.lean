-- Prove2me | solution 1 for IsArtinianRing.exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/462ae884-f49a-5f31-9424-fc14c1f96115

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

namespace P2mHilbert90Artin

open Function Finset

variable {E : Type*} [CommRing E]

section Resolvent

variable (θ : E →+* E) (c : E)

def P (i : ℕ) : E := ((List.range i).map fun j => θ^[j] c).prod

theorem P_zero : P θ c 0 = 1 := by simp [P]

theorem P_succ (i : ℕ) : P θ c (i + 1) = P θ c i * θ^[i] c := by
  simp [P, List.range_succ]

theorem mul_map_P (i : ℕ) : c * θ (P θ c i) = P θ c (i + 1) := by
  induction i with
  | zero => rw [P_zero, map_one, mul_one, P_succ, P_zero, one_mul]; rfl
  | succ i ih =>
      rw [P_succ, map_mul, ← mul_assoc, ih, P_succ θ c (i + 1)]
      congr 1
      exact (Function.iterate_succ_apply' θ i c).symm

def Φ (k : ℕ) : E →+ E where
  toFun x := ∑ i ∈ range k, P θ c i * θ^[i] x
  map_zero' := by simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← RingHom.coe_pow, map_add, mul_add]

theorem Φ_apply (k : ℕ) (x : E) : Φ θ c k x = ∑ i ∈ range k, P θ c i * θ^[i] x := rfl

theorem mul_map_Φ (k : ℕ) (hPk : P θ c k = 1) (hθ : ∀ x : E, θ^[k] x = x) (x : E) :
    c * θ (Φ θ c k x) = Φ θ c k x := by
  rw [Φ_apply, map_sum, Finset.mul_sum]
  have h1 : ∀ i ∈ range k, c * θ (P θ c i * θ^[i] x) = P θ c (i + 1) * θ^[i + 1] x := by
    intro i _
    rw [map_mul, ← mul_assoc, mul_map_P, Function.iterate_succ_apply']
  rw [Finset.sum_congr rfl h1]
  have h2 := Finset.sum_range_succ' (fun i => P θ c i * θ^[i] x) k
  have h3 := Finset.sum_range_succ (fun i => P θ c i * θ^[i] x) k
  rw [h3, hPk, hθ, P_zero, Function.iterate_zero, id, one_mul] at h2
  exact (add_right_cancel h2).symm

theorem P_eq_of_prod (k : ℕ) (hc : ((List.range k).map fun i => θ^[i] c).prod = 1) : P θ c k = 1 := hc

end Resolvent

section Factors

variable [IsArtinianRing E] [IsReduced E]

abbrev ι (E : Type*) [CommRing E] : Type _ := MaximalSpectrum E

noncomputable scoped instance : Fintype (ι E) := Fintype.ofFinite _

abbrev π (I : ι E) : E →+* E ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal

theorem π_eq_zero_iff (I : ι E) (x : E) : π I x = 0 ↔ x ∈ I.asIdeal := Ideal.Quotient.eq_zero_iff_mem

theorem equivPi_apply (x : E) (I : ι E) : IsArtinianRing.equivPi E x I = π I x := rfl

theorem eq_of_forall_π_eq {x y : E} (h : ∀ I : ι E, π I x = π I y) : x = y :=
  (IsArtinianRing.equivPi E).injective (funext fun I => by rw [equivPi_apply, equivPi_apply, h I])

theorem exists_forall_π_eq (y : ∀ I : ι E, E ⧸ I.asIdeal) : ∃ x : E, ∀ I, π I x = y I :=
  ⟨(IsArtinianRing.equivPi E).symm y, fun I => by
    rw [← equivPi_apply, AlgEquiv.apply_symm_apply]⟩

theorem isUnit_iff_forall_π_ne_zero (x : E) : IsUnit x ↔ ∀ I : ι E, π I x ≠ 0 := by
  constructor
  · intro hx I h
    exact (hx.map (π I)).ne_zero h
  · intro h
    by_contra hx
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
    exact h ⟨M, hM⟩ ((π_eq_zero_iff _ _).2 hxM)

end Factors

section Perm

variable [IsArtinianRing E] [IsReduced E] (θ : E →+* E) {k : ℕ} (hk : 0 < k)
  (hθ : ∀ x : E, θ^[k] x = x)

include hk hθ

theorem θ_pow_k : θ ^ k = 1 := RingHom.ext fun x => by rw [RingHom.coe_pow]; exact hθ x

theorem θ_bijective : Function.Bijective θ := by
  have hki : Function.Bijective (θ^[k]) := by
    have : (θ^[k]) = id := funext hθ
    rw [this]; exact Function.bijective_id
  obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [hn] at hki
  refine ⟨?_, ?_⟩
  · rw [Function.iterate_succ] at hki
    exact hki.1.of_comp
  · rw [Function.iterate_succ'] at hki
    exact hki.2.of_comp

theorem θ_pow_surjective (i : ℕ) : Function.Surjective (θ ^ i) := by
  rw [RingHom.coe_pow]
  exact (θ_bijective θ hk hθ).2.iterate i

def τ (I : ι E) : ι E :=
  ⟨I.asIdeal.comap θ, Ideal.comap_isMaximal_of_surjective θ (θ_bijective θ hk hθ).2⟩

theorem τ_asIdeal (I : ι E) : (τ θ hk hθ I).asIdeal = I.asIdeal.comap θ := rfl

theorem τ_iterate_asIdeal (i : ℕ) (I : ι E) : ((τ θ hk hθ)^[i] I).asIdeal = I.asIdeal.comap (θ ^ i) := by
  induction i with
  | zero => rw [Function.iterate_zero, id, pow_zero]; exact (Ideal.comap_id _).symm
  | succ i ih =>
      rw [Function.iterate_succ_apply', τ_asIdeal, ih, pow_succ, Ideal.comap_comap]
      rfl

theorem π_τ_iterate_eq_zero_iff (i : ℕ) (I : ι E) (x : E) :
    π ((τ θ hk hθ)^[i] I) x = 0 ↔ π I (θ^[i] x) = 0 := by
  rw [π_eq_zero_iff, π_eq_zero_iff, τ_iterate_asIdeal, Ideal.mem_comap, RingHom.coe_pow]

theorem τ_iterate_k (I : ι E) : (τ θ hk hθ)^[k] I = I := by
  apply MaximalSpectrum.ext
  rw [τ_iterate_asIdeal, θ_pow_k θ hk hθ]
  exact Ideal.comap_id I.asIdeal

theorem τ_isPeriodicPt (I : ι E) : Function.IsPeriodicPt (τ θ hk hθ) k I := τ_iterate_k θ hk hθ I

theorem τ_injective : Function.Injective (τ θ hk hθ) := by
  have h : Function.LeftInverse ((τ θ hk hθ)^[k - 1]) (τ θ hk hθ) := fun I => by
    rw [← Function.iterate_succ_apply]
    show (τ θ hk hθ)^[k - 1 + 1] I = I
    rw [Nat.sub_add_cancel hk, τ_iterate_k]
  exact h.injective

theorem τ_iterate_injective (i : ℕ) : Function.Injective ((τ θ hk hθ)^[i]) :=
  (τ_injective θ hk hθ).iterate i

theorem minimalPeriod_pos (I : ι E) : 0 < Function.minimalPeriod (τ θ hk hθ) I :=
  Function.minimalPeriod_pos_of_mem_periodicPts ⟨k, hk, τ_isPeriodicPt θ hk hθ I⟩

private theorem _root_.P2mHilbert90Artin.minimalPeriod_dvd (I : ι E) : Function.minimalPeriod (τ θ hk hθ) I ∣ k :=
  (τ_isPeriodicPt θ hk hθ I).minimalPeriod_dvd

p2m_export "P2mHilbert90Artin" "minimalPeriod_dvd"

def θbar (I : ι E) : E ⧸ (τ θ hk hθ I).asIdeal →+* E ⧸ I.asIdeal :=
  Ideal.quotientMap I.asIdeal θ le_rfl

theorem θbar_mk (I : ι E) (x : E) : θbar θ hk hθ I (π (τ θ hk hθ I) x) = π I (θ x) := by
  rw [θbar, Ideal.quotientMap_mk]

theorem θbar_injective (I : ι E) : Function.Injective (θbar θ hk hθ I) :=
  Ideal.quotientMap_injective

theorem π_τ_ne_zero_iff {c : E} (hc : IsUnit c) {w : E} (hw : c * θ w = w) (I : ι E) :
    π (τ θ hk hθ I) w ≠ 0 ↔ π I w ≠ 0 := by
  have h1 : π I w = π I c * θbar θ hk hθ I (π (τ θ hk hθ I) w) := by
    rw [θbar_mk, ← map_mul, hw]
  rw [h1]
  have hcI : π I c ≠ 0 := (isUnit_iff_forall_π_ne_zero c).1 hc I
  constructor
  · intro h h0
    rcases mul_eq_zero.1 h0 with h2 | h2
    · exact hcI h2
    · apply h
      apply θbar_injective θ hk hθ I
      rw [h2, map_zero]
  · intro h h0
    apply h
    rw [h0, map_zero, mul_zero]

theorem π_τ_iterate_ne_zero_iff {c : E} (hc : IsUnit c) {w : E} (hw : c * θ w = w) (i : ℕ) (I : ι E) :
    π ((τ θ hk hθ)^[i] I) w ≠ 0 ↔ π I w ≠ 0 := by
  induction i generalizing I with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', π_τ_ne_zero_iff θ hk hθ hc hw, ih]

theorem π_iterate_eq_zero_of_supported {I₀ : ι E} {x : E} (hx : ∀ J, J ≠ I₀ → π J x = 0)
    (i : ℕ) (J : ι E) (hJ : (τ θ hk hθ)^[i] J ≠ I₀) : π J (θ^[i] x) = 0 := by
  rw [← π_τ_iterate_eq_zero_iff θ hk hθ]
  exact hx _ hJ

end Perm

section OneFactor

variable [IsArtinianRing E] [IsReduced E] (θ : E →+* E) {k : ℕ} (hk : 0 < k)
  (hθ : ∀ x : E, θ^[k] x = x)
  (hfree : ∀ e : E, IsIdempotentElem e → e ≠ 0 → ∀ i : ℕ, 0 < i → i < k →
    ¬ ∀ x : E, θ^[i] (e * x) = e * x)

include hk hθ

noncomputable def ρbar (I₀ : ι E) : E ⧸ I₀.asIdeal →+* E ⧸ I₀.asIdeal :=
  Ideal.quotientMap I₀.asIdeal (θ ^ Function.minimalPeriod (τ θ hk hθ) I₀) (le_of_eq (by
    rw [← τ_iterate_asIdeal θ hk hθ, Function.iterate_minimalPeriod]))

theorem ρbar_mk (I₀ : ι E) (x : E) :
    ρbar θ hk hθ I₀ (π I₀ x) = π I₀ (θ^[Function.minimalPeriod (τ θ hk hθ) I₀] x) := by
  rw [ρbar, Ideal.quotientMap_mk, RingHom.coe_pow]

theorem ρbar_iterate_mk (I₀ : ι E) (q : ℕ) (x : E) :
    (ρbar θ hk hθ I₀)^[q] (π I₀ x) = π I₀ (θ^[Function.minimalPeriod (τ θ hk hθ) I₀ * q] x) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply', ih, ρbar_mk, ← Function.iterate_add_apply, Nat.mul_succ,
        Nat.add_comm]

theorem ρbar_injective (I₀ : ι E) : Function.Injective (ρbar θ hk hθ I₀) :=
  RingHom.injective _

theorem exists_idempotent (I₀ : ι E) :
    ∃ e : E, IsIdempotentElem e ∧ e ≠ 0 ∧ π I₀ e = 1 ∧ ∀ J, J ≠ I₀ → π J e = 0 := by
  classical
  obtain ⟨e, he⟩ := exists_forall_π_eq (E := E) (fun J => if J = I₀ then 1 else 0)
  have h1 : π I₀ e = 1 := by rw [he]; simp
  have h0 : ∀ J, J ≠ I₀ → π J e = 0 := fun J hJ => by rw [he]; simp [hJ]
  refine ⟨e, ?_, ?_, h1, h0⟩
  · apply eq_of_forall_π_eq
    intro J
    by_cases hJ : J = I₀
    · subst hJ; rw [map_mul, h1, mul_one]
    · rw [map_mul, h0 J hJ, mul_zero]
  · intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1

include hfree in

theorem ρbar_iterate_ne_id (I₀ : ι E) {p : ℕ} (hp : 0 < p)
    (hpk : Function.minimalPeriod (τ θ hk hθ) I₀ * p < k) :
    ¬ ∀ y : E ⧸ I₀.asIdeal, (ρbar θ hk hθ I₀)^[p] y = y := by
  intro hid
  set r := Function.minimalPeriod (τ θ hk hθ) I₀ with hr
  obtain ⟨e, he, he0, he1, hesupp⟩ := exists_idempotent θ hk hθ I₀
  have hrp : 0 < r * p := Nat.mul_pos (minimalPeriod_pos θ hk hθ I₀) hp
  refine hfree e he he0 (r * p) hrp hpk fun x => ?_
  apply eq_of_forall_π_eq
  intro J
  by_cases hJ : J = I₀
  · subst hJ
    rw [← ρbar_iterate_mk, hid]
  · have hτJ : (τ θ hk hθ)^[r * p] J ≠ I₀ := by
      intro h
      have hper : (τ θ hk hθ)^[r * p] I₀ = I₀ :=
        (Function.isPeriodicPt_minimalPeriod (τ θ hk hθ) I₀).mul_const p
      exact hJ (τ_iterate_injective θ hk hθ (r * p) (h.trans hper.symm))
    have h1 : π J (θ^[r * p] (e * x)) = 0 := by
      rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow,
        π_iterate_eq_zero_of_supported θ hk hθ hesupp (r * p) J hτJ, zero_mul]
    have h2 : π J (e * x) = 0 := by rw [map_mul, hesupp J hJ, zero_mul]
    rw [h1, h2]

include hfree in

theorem ρbar_pow_injective (I₀ : ι E) :
    Function.Injective fun q : Fin (k / Function.minimalPeriod (τ θ hk hθ) I₀) =>
      ((ρbar θ hk hθ I₀) ^ (q : ℕ)).toMonoidHom := by
  set r := Function.minimalPeriod (τ θ hk hθ) I₀ with hr
  intro q q' hqq'
  simp only at hqq'
  have hfun : ∀ y, (ρbar θ hk hθ I₀)^[(q : ℕ)] y = (ρbar θ hk hθ I₀)^[(q' : ℕ)] y := fun y => by
    have := congrArg (fun f : (E ⧸ I₀.asIdeal) →* (E ⧸ I₀.asIdeal) => f y) hqq'
    simpa [RingHom.coe_pow] using this

  by_contra hne
  have key : ∀ (a b : ℕ), a < b → b < k / r → (∀ y, (ρbar θ hk hθ I₀)^[b] y = (ρbar θ hk hθ I₀)^[a] y) → False := by
    intro a b hab hb hy
    have hp : 0 < b - a := Nat.sub_pos_of_lt hab
    have hpk : r * (b - a) < k := by
      have hrk : r ∣ k := minimalPeriod_dvd θ hk hθ I₀
      have h1 : r * (b - a) ≤ r * (k / r - 1) := Nat.mul_le_mul_left r (by omega)
      have h2 : r * (k / r) = k := Nat.mul_div_cancel' hrk
      have hr0 : 0 < r := minimalPeriod_pos θ hk hθ I₀
      have h3 : r * (k / r - 1) < k := by
        rw [Nat.mul_sub, mul_one, h2]
        exact Nat.sub_lt hk hr0
      omega
    refine ρbar_iterate_ne_id θ hk hθ hfree I₀ hp hpk fun y => ?_
    have h' := hy y
    rw [show b = a + (b - a) by omega, Function.iterate_add_apply] at h'
    exact (ρbar_injective θ hk hθ I₀).iterate a h'
  rcases lt_or_gt_of_ne (fun h : (q : ℕ) = q' => hne (Fin.ext h)) with hlt | hgt
  · exact key q q' hlt q'.2 fun y => (hfun y).symm
  · exact key q' q hgt q.2 hfun

omit [IsArtinianRing E] [IsReduced E] in
theorem isUnit_iterate {c : E} (hc : IsUnit c) (j : ℕ) : IsUnit (θ^[j] c) := by
  induction j with
  | zero => exact hc
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.map θ

omit [IsArtinianRing E] [IsReduced E] in
theorem isUnit_P {c : E} (hc : IsUnit c) (i : ℕ) : IsUnit (P θ c i) := by
  induction i with
  | zero => rw [P_zero]; exact isUnit_one
  | succ i ih => rw [P_succ]; exact ih.mul (isUnit_iterate θ hk hθ hc i)

include hfree in

theorem exists_supported_π_Φ_ne_zero (c : E) (hc : IsUnit c) (I₀ : ι E) :
    ∃ x : E, (∀ J, J ≠ I₀ → π J x = 0) ∧ π I₀ (Φ θ c k x) ≠ 0 := by
  classical
  set r := Function.minimalPeriod (τ θ hk hθ) I₀ with hr
  set m := k / r with hm
  have hr0 : 0 < r := minimalPeriod_pos θ hk hθ I₀
  have hrm : r * m = k := Nat.mul_div_cancel' (minimalPeriod_dvd θ hk hθ I₀)
  set F := E ⧸ I₀.asIdeal
  set ρ := ρbar θ hk hθ I₀ with hρ

  set a : Fin m → F := fun q => π I₀ (P θ c (r * q)) with ha
  have ha0 : ∀ q, a q ≠ 0 := fun q =>
    (isUnit_iff_forall_π_ne_zero _).1 (isUnit_P θ hk hθ hc _) I₀

  have hli : LinearIndependent F fun q : Fin m => ((ρ ^ (q : ℕ)).toMonoidHom : F → F) :=
    (linearIndependent_monoidHom F F).comp _ (ρbar_pow_injective θ hk hθ hfree I₀)
  have hy : ∃ y : F, ∑ q : Fin m, a q * (ρ^[(q : ℕ)]) y ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : ∑ q : Fin m, a q • ((ρ ^ (q : ℕ)).toMonoidHom : F → F) = 0 := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_pow]
      exact h y
    have h0 := (Fintype.linearIndependent_iff.1 hli) a hsum ⟨0, Nat.div_pos
      (Nat.le_of_dvd hk (minimalPeriod_dvd θ hk hθ I₀)) hr0⟩
    exact ha0 _ h0
  obtain ⟨y, hy⟩ := hy

  obtain ⟨e, -, -, he1, hesupp⟩ := exists_idempotent θ hk hθ I₀
  obtain ⟨x', hx'⟩ := Ideal.Quotient.mk_surjective y
  set x : E := e * x' with hxdef
  have hx0 : π I₀ x = y := by rw [hxdef, map_mul, he1, one_mul]; exact hx'
  have hxs : ∀ J, J ≠ I₀ → π J x = 0 := fun J hJ => by rw [hxdef, map_mul, hesupp J hJ, zero_mul]
  refine ⟨x, hxs, ?_⟩

  have hterm : ∀ i, π I₀ (P θ c i * θ^[i] x) = if r ∣ i then π I₀ (P θ c i) * ρ^[i / r] y else 0 := by
    intro i
    split_ifs with hi
    · obtain ⟨q, rfl⟩ := hi
      rw [map_mul, Nat.mul_div_cancel_left q hr0, ← hx0, hρ, ρbar_iterate_mk]
    · rw [map_mul]
      have : π I₀ (θ^[i] x) = 0 := by
        refine π_iterate_eq_zero_of_supported θ hk hθ hxs i I₀ fun h => hi ?_
        exact (Function.isPeriodicPt_iff_minimalPeriod_dvd.1 h)
      rw [this, mul_zero]
  have hΦ : π I₀ (Φ θ c k x) = ∑ q : Fin m, a q * ρ^[(q : ℕ)] y := by
    rw [Φ_apply, map_sum]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

    rw [← hrm]
    symm
    refine Finset.sum_nbij (fun q : Fin m => r * (q : ℕ)) ?_ ?_ ?_ ?_
    · intro q _
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mul_lt_mul_of_pos_left q.2 hr0, dvd_mul_right r q⟩
    · intro q _ q' _ h
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hr0 h)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      obtain ⟨hik, q, rfl⟩ := hi
      refine ⟨⟨q, ?_⟩, by simp, rfl⟩
      exact Nat.lt_of_mul_lt_mul_left hik
    · intro q _
      simp only [ha, Nat.mul_div_cancel_left _ hr0]
  rw [hΦ]
  exact hy

end OneFactor

section Assembly

variable [IsArtinianRing E] [IsReduced E] (θ : E →+* E) {k : ℕ} (hk : 0 < k)
  (hθ : ∀ x : E, θ^[k] x = x)
  (hfree : ∀ e : E, IsIdempotentElem e → e ≠ 0 → ∀ i : ℕ, 0 < i → i < k →
    ¬ ∀ x : E, θ^[i] (e * x) = e * x)

include hk hθ

def orbitSetoid : Setoid (ι E) where
  r I J := ∃ i, (τ θ hk hθ)^[i] I = J
  iseqv := by
    refine ⟨fun I => ⟨0, rfl⟩, ?_, ?_⟩
    · rintro I J ⟨i, rfl⟩
      obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < k ∧ i = k * q + s :=
        ⟨i / k, i % k, Nat.mod_lt i hk, (Nat.div_add_mod i k).symm⟩
      refine ⟨k - s, ?_⟩
      rw [← Function.iterate_add_apply]
      have : k - s + (k * q + s) = k * (q + 1) := by rw [Nat.mul_succ]; omega
      rw [this]
      exact (τ_isPeriodicPt θ hk hθ I).mul_const (q + 1)
    · rintro I J M ⟨i, rfl⟩ ⟨j, rfl⟩
      exact ⟨j + i, Function.iterate_add_apply _ _ _ _⟩

theorem orbit_symm {I J : ι E} (h : (orbitSetoid θ hk hθ).r I J) : (orbitSetoid θ hk hθ).r J I :=
  (orbitSetoid θ hk hθ).iseqv.symm h

include hfree in

theorem exists_isUnit_Φ (c : E) (hc : IsUnit c) (hPk : P θ c k = 1) : ∃ x : E, IsUnit (Φ θ c k x) := by
  classical

  have h1 := fun I₀ => exists_supported_π_Φ_ne_zero θ hk hθ hfree c hc I₀
  choose xI hxs hxne using h1

  letI S : Setoid (ι E) := orbitSetoid θ hk hθ
  let rep : ι E → ι E := fun J => (⟦J⟧ : Quotient S).out
  have hrep : ∀ J, (rep J) ≈ J := fun J => Quotient.exact (Quotient.out_eq (⟦J⟧ : Quotient S))
  have hrep_eq : ∀ I J, I ≈ J → rep I = rep J := fun I J h => by
    show (⟦I⟧ : Quotient S).out = (⟦J⟧ : Quotient S).out
    rw [Quotient.sound h]
  let T : Finset (ι E) := Finset.univ.image rep
  refine ⟨∑ I ∈ T, xI I, ?_⟩
  rw [isUnit_iff_forall_π_ne_zero]
  intro J
  rw [map_sum, map_sum]

  have hvan : ∀ I ∈ T, I ≠ rep J → π J (Φ θ c k (xI I)) = 0 := by
    intro I hI hIJ
    obtain ⟨J', -, rfl⟩ := Finset.mem_image.1 hI
    rw [Φ_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul]
    have : π J (θ^[i] (xI (rep J'))) = 0 := by
      refine π_iterate_eq_zero_of_supported θ hk hθ (hxs (rep J')) i J fun h => hIJ ?_

      have hJ : J ≈ rep J' := ⟨i, h⟩
      calc rep J' = rep (rep J') := (hrep_eq _ _ (hrep J')).symm
        _ = rep J := (hrep_eq _ _ hJ).symm
    rw [this, mul_zero]
  rw [Finset.sum_eq_single (rep J) hvan (fun h => (h (Finset.mem_image.2 ⟨J, Finset.mem_univ _, rfl⟩)).elim)]

  obtain ⟨i, hi⟩ := hrep J
  have h := (π_τ_iterate_ne_zero_iff θ hk hθ hc (mul_map_Φ θ c k hPk hθ (xI (rep J))) i (rep J)).2
    (hxne (rep J))
  rwa [hi] at h

include hfree in
theorem main (c : Eˣ) (hc : ((List.range k).map fun i => θ^[i] (c : E)).prod = 1) :
    ∃ z : Eˣ, (z : E) = c * θ z := by
  have hPk : P θ (c : E) k = 1 := hc
  obtain ⟨x, hx⟩ := exists_isUnit_Φ θ hk hθ hfree (c : E) c.isUnit hPk
  refine ⟨hx.unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact (mul_map_Φ θ (c : E) k hPk hθ x).symm

end Assembly

end P2mHilbert90Artin
p2m_reactivate "P2MW.S_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one.P2mHilbert90Artin"

theorem solution
    (E : Type) [CommRing E] [IsArtinianRing E] [IsReduced E]
    (θ : E →+* E) (k : ℕ) (hk : 0 < k) (hθ : ∀ x : E, θ^[k] x = x)
    (hfree : ∀ e : E, IsIdempotentElem e → e ≠ 0 → ∀ i : ℕ, 0 < i → i < k →
      ¬ ∀ x : E, θ^[i] (e * x) = e * x)
    (c : Eˣ) (hc : ((List.range k).map fun i => θ^[i] (c : E)).prod = 1) :
    ∃ z : Eˣ, (z : E) = c * θ z :=
  P2mHilbert90Artin.main θ hk hθ hfree c hc

end S_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one
end P2MW
export P2MW.S_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one (solution)
