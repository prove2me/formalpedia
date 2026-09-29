-- Prove2me | solution 1 for IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c1d6f6ff-933c-5a66-bcd9-af01b22a2e4f

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_IsLocalRing_isPrincipal_of_isPrincipal_map_adicCompletion
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_Ideal_map_colon_eq_colon_map_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace GlueWs27
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

section PowerSeriesAux
variable {A : Type*} [CommRing A]

theorem ps_eq_zero_of_X_mul_eq_zero (p : PowerSeries A) (h : PowerSeries.X * p = 0) : p = 0 := by
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  rw [PowerSeries.coeff_succ_X_mul, map_zero] at this
  rw [this, map_zero]

theorem ps_eq_zero_of_X_pow_mul_eq_zero (p : PowerSeries A) (n : ℕ)
    (h : PowerSeries.X ^ n * p = 0) : p = 0 := by
  induction n with
  | zero => rwa [pow_zero, one_mul] at h
  | succ n ih =>
      apply ih
      apply ps_eq_zero_of_X_mul_eq_zero
      rw [← mul_assoc, ← pow_succ', h]

theorem ps_mem_span_C_of_forall_coeff (a : A) (p : PowerSeries A)
    (h : ∀ n, PowerSeries.coeff n p ∈ Ideal.span {a}) : p ∈ Ideal.span {PowerSeries.C a} := by
  choose b hb using fun n => Ideal.mem_span_singleton'.mp (h n)
  rw [Ideal.mem_span_singleton']
  refine ⟨PowerSeries.mk b, ?_⟩
  ext n
  rw [mul_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm, hb]

end PowerSeriesAux

section MvAux
variable {W : Type*} [CommRing W]

theorem mv_mem_span_X_of_constantCoeff_eq_zero (G : MvPowerSeries (Fin 2) W)
    (hG : MvPowerSeries.constantCoeff G = 0) :
    G ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  classical
  let G₁ : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then 0 else G m
  have hc₁ : ∀ m, MvPowerSeries.coeff m G₁ = if m 0 = 0 then 0 else MvPowerSeries.coeff m G := fun m => rfl
  have h1 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ G₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hc₁, if_pos hm]
  have h2 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ (G - G₁) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [map_sub, hc₁]
    by_cases h0 : m 0 = 0
    · rw [if_pos h0, sub_zero]
      have hm0 : m = 0 := by
        ext i
        fin_cases i
        · exact h0
        · exact hm
      rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG]
    · rw [if_neg h0, sub_self]
  have hGsplit : G = G₁ + (G - G₁) := by ring
  rw [hGsplit, Ideal.span_insert]
  exact Submodule.add_mem_sup (Ideal.mem_span_singleton.mpr h1) (Ideal.mem_span_singleton.mpr h2)

theorem mv_mem_span_of_not_isUnit [IsDomain W] [IsDiscreteValuationRing W] (π : W)
    (hπ : Irreducible π) (F : MvPowerSeries (Fin 2) W) (hF : ¬ IsUnit F) :
    F ∈ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  have hc : ¬ IsUnit (MvPowerSeries.constantCoeff F) :=
    fun h => hF (MvPowerSeries.isUnit_iff_constantCoeff.mpr h)
  have hmem : MvPowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal W :=
    (IsLocalRing.mem_maximalIdeal _).mpr hc
  rw [hπ.maximalIdeal_eq] at hmem
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hsplit : F = MvPowerSeries.C π * MvPowerSeries.C a +
      (F - MvPowerSeries.C (MvPowerSeries.constantCoeff F)) := by
    rw [← map_mul, mul_comm, ha]; ring
  have hrest : F - MvPowerSeries.C (MvPowerSeries.constantCoeff F)
      ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
    apply mv_mem_span_X_of_constantCoeff_eq_zero
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  rw [hsplit, Ideal.span_insert]
  exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) hrest

end MvAux

theorem span_pair_pow_le {T : Type*} [CommRing T] (a b : T) (n : ℕ) :
    (Ideal.span {a, b}) ^ n ≤ Ideal.span {a ^ n} ⊔ Ideal.span {b} := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Ideal.span_singleton_one, top_sup_eq]; exact le_top
  | succ n ih =>
      rw [pow_succ]
      refine (Ideal.mul_mono_left ih).trans ?_
      rw [Ideal.sup_mul, Ideal.span_insert, Ideal.mul_sup, Ideal.mul_sup]
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]; exact le_sup_left
      · exact Ideal.mul_le_right.trans le_sup_right
      · exact Ideal.mul_le_left.trans le_sup_right
      · exact Ideal.mul_le_left.trans le_sup_right

theorem span_triple_units {T : Type*} [CommRing T] (a b c u v : T) (hu : IsUnit u) (hv : IsUnit v) :
    Ideal.span {a, b * u, c * v} = Ideal.span {a, b, c} := by
  rw [Ideal.span_insert, Ideal.span_insert, Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit hu, Ideal.span_singleton_mul_right_unit hv]

theorem span_pair_unit {T : Type*} [CommRing T] (a b u : T) (hu : IsUnit u) :
    Ideal.span {a, b * u} = Ideal.span {a, b} := by
  rw [Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_mul_right_unit hu]

section Model
variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
  (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)

local notation "MM" => UVCrossingModel W (π ^ E)
local notation "πM" => UVCrossingModel.const (π ^ E) π
local notation "UU" => UVCrossingModel.U (π ^ E)
local notation "VV" => UVCrossingModel.V (π ^ E)

include hπ in
theorem span_pi_isMaximal : (Ideal.span {π}).IsMaximal := by
  rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal W

theorem U_mul_V_eq_pow : UU * VV = πM ^ E := by
  rw [ModularCurve.UVCrossingModel.U_mul_V]
  show constHom (π ^ E) (π ^ E) = (constHom (π ^ E) π) ^ E
  rw [map_pow]

include hπ in

theorem mem_span_of_not_isUnit (f : MM) (hf : ¬ IsUnit f) : f ∈ Ideal.span {πM, UU, VV} := by
  obtain ⟨F, rfl⟩ := UVCrossingModel.mk_surjective (π ^ E) f
  have hF : ¬ IsUnit F := fun h => hf (h.map _)
  have hmem := mv_mem_span_of_not_isUnit π hπ F hF
  have himg : Ideal.map (UVCrossingModel.mk (π ^ E))
      (Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})
      = Ideal.span {πM, UU, VV} := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← himg]
  exact Ideal.mem_map_of_mem _ hmem

include hπ hE in

theorem exists_tau (P Q : MM) (e : (MM ⧸ Ideal.span {P}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heQ : e (Ideal.Quotient.mk _ Q) = PowerSeries.X) (heP : e (Ideal.Quotient.mk _ P) = 0)
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (UVCrossingModel.const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w)) :
    ∃ τ : MM →+* PowerSeries (W ⧸ Ideal.span {π}),
      Function.Surjective τ ∧ τ P = 0 ∧ τ Q = PowerSeries.X ∧
      (∀ w : W, τ (UVCrossingModel.const (π ^ E) w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w)) ∧
      RingHom.ker τ = Ideal.span {πM, P} := by
  have hle : Ideal.span {π ^ E} ≤ Ideal.span {π} := by
    rw [Ideal.span_singleton_le_span_singleton]; exact dvd_pow_self π (by omega)
  let red : W ⧸ Ideal.span {π ^ E} →+* W ⧸ Ideal.span {π} :=
    Ideal.Quotient.lift (Ideal.span {π ^ E}) (Ideal.Quotient.mk (Ideal.span {π}))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha))
  have hred_mk : ∀ w, red (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ w :=
    fun w => Ideal.Quotient.lift_mk _ _ _
  have hred_surj : Function.Surjective red := by
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ w, hred_mk w⟩
  let τ : MM →+* PowerSeries (W ⧸ Ideal.span {π}) :=
    (PowerSeries.map red).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {P})))
  have hτ_apply : ∀ f : MM, τ f = PowerSeries.map red (e (Ideal.Quotient.mk _ f)) := fun f => rfl
  refine ⟨τ, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    have hms : Function.Surjective (PowerSeries.map red) := fun p => by
      refine ⟨PowerSeries.mk fun n => (hred_surj (PowerSeries.coeff n p)).choose, ?_⟩
      ext n
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
      exact (hred_surj (PowerSeries.coeff n p)).choose_spec
    obtain ⟨p', hp'⟩ := hms p
    obtain ⟨y, hy⟩ := e.surjective p'
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨f, by rw [hτ_apply, hy, hp']⟩
  · rw [hτ_apply, heP, map_zero]
  · rw [hτ_apply, heQ, PowerSeries.map_X]
  · intro w; rw [hτ_apply, heC, PowerSeries.map_C, hred_mk]
  · apply le_antisymm
    · intro f hf
      rw [RingHom.mem_ker, hτ_apply] at hf
      have hcoef : ∀ n, PowerSeries.coeff n (e (Ideal.Quotient.mk _ f))
          ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {π ^ E}) π} := by
        intro n
        have hn := congrArg (PowerSeries.coeff n) hf
        rw [PowerSeries.coeff_map, map_zero] at hn
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (PowerSeries.coeff n (e (Ideal.Quotient.mk _ f)))
        rw [← hc, hred_mk, Ideal.Quotient.eq_zero_iff_mem] at hn
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hn
        rw [← hc, ← hd, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      have hqmem := ps_mem_span_C_of_forall_coeff _ _ hcoef
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hqmem
      have hmkf : Ideal.Quotient.mk (Ideal.span {P}) f
          = e.symm r * Ideal.Quotient.mk (Ideal.span {P}) πM := by
        apply e.injective
        rw [map_mul, e.apply_symm_apply, heC, hr]
      obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (e.symm r)
      have hdiff : f - g * πM ∈ Ideal.span {P} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hg, hmkf, sub_self]
      have hf' : f = g * πM + (f - g * πM) := by ring
      rw [hf', Ideal.span_insert]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) hdiff
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hx with hx | hx
      · rw [hx, hτ_apply, heC, PowerSeries.map_C, hred_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self π), map_zero]
      · rw [hx, hτ_apply, heP, map_zero]

include hπ hE in
theorem isPrime_and_notMem (P Q : MM) (e : (MM ⧸ Ideal.span {P}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heQ : e (Ideal.Quotient.mk _ Q) = PowerSeries.X) (heP : e (Ideal.Quotient.mk _ P) = 0)
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (UVCrossingModel.const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w)) :
    (Ideal.span {πM, P}).IsPrime ∧ Q ∉ Ideal.span {πM, P} := by
  obtain ⟨τ, -, -, hQ, -, hker⟩ := exists_tau π hπ E hE P Q e heQ heP heC
  haveI : (Ideal.span {π}).IsMaximal := span_pi_isMaximal π hπ
  haveI : Nontrivial (W ⧸ Ideal.span {π}) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  rw [← hker]
  refine ⟨RingHom.ker_isPrime τ, ?_⟩
  rw [RingHom.mem_ker, hQ]
  exact PowerSeries.X_ne_zero

include hπ hE in
theorem isPrime_span_pi_U_and : (Ideal.span {πM, UU}).IsPrime ∧ VV ∉ Ideal.span {πM, UU} := by
  obtain ⟨e, heV, heU, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (π ^ E)
  exact isPrime_and_notMem π hπ E hE UU VV e heV heU heC

include hπ hE in
theorem isPrime_span_pi_V_and : (Ideal.span {πM, VV}).IsPrime ∧ UU ∉ Ideal.span {πM, VV} := by
  obtain ⟨e, heU, heV, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries (π ^ E)
  exact isPrime_and_notMem π hπ E hE VV UU e heU heV heC

theorem mem_span_of_forall_mul_mem (P Q : MM) (hPQ : P * Q = πM ^ E)
    {A : Type*} [CommRing A] (e : (MM ⧸ Ideal.span {P}) ≃+* PowerSeries A)
    (heQ : e (Ideal.Quotient.mk _ Q) = PowerSeries.X)
    (f : MM) (hf : ∀ s ∈ (Ideal.span {πM, Q}) ^ (E - 1), f * s ∈ (Ideal.span {πM, P}) ^ E) :
    f ∈ Ideal.span {P} := by
  have hQ : Q ^ (E - 1) ∈ (Ideal.span {πM, Q}) ^ (E - 1) :=
    Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _
  have h1 := hf _ hQ
  have h2 : (Ideal.span {πM, P}) ^ E ≤ Ideal.span {P} := by
    refine (span_pair_pow_le πM P E).trans (sup_le ?_ le_rfl)
    rw [Ideal.span_singleton_le_iff_mem, ← hPQ]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h3 : f * Q ^ (E - 1) ∈ Ideal.span {P} := h2 h1
  have h4 : Ideal.Quotient.mk (Ideal.span {P}) (f * Q ^ (E - 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have h5 : PowerSeries.X ^ (E - 1) * e (Ideal.Quotient.mk _ f) = 0 := by
    have := congrArg e h4
    simp only [map_mul, map_pow, heQ, map_zero] at this
    rw [mul_comm] at this
    exact this
  have h6 := ps_eq_zero_of_X_pow_mul_eq_zero _ _ h5
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact e.injective (by rw [h6, map_zero])

include hE in
theorem mul_mem_pow_of_mem (P Q : MM) (hPQ : P * Q = πM ^ E)
    (s : MM) (hs : s ∈ (Ideal.span {πM, Q}) ^ (E - 1)) : P * s ∈ (Ideal.span {πM, P}) ^ E := by
  have h1 := span_pair_pow_le πM Q (E - 1) hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [mul_add]
  apply Ideal.add_mem
  · have hE' : E - 1 + 1 = E := Nat.sub_add_cancel hE
    have hpow : (Ideal.span {πM, P}) ^ E = (Ideal.span {πM, P}) ^ (E - 1) * Ideal.span {πM, P} := by
      rw [← Submodule.pow_succ, hE']
    have hmem : πM ^ (E - 1) * P ∈ (Ideal.span {πM, P}) ^ E := by
      rw [hpow]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)
        (Ideal.subset_span (by simp))
    have e1 : P * (a' * πM ^ (E - 1)) = a' * (πM ^ (E - 1) * P) := by ring
    rw [e1]
    exact Ideal.mul_mem_left _ _ hmem
  · have e2 : P * (b' * Q) = b' * (P * Q) := by ring
    rw [e2, hPQ]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)

end Model
end GlueWs27

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel GlueWs27 in
theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* UVCrossingModel W (π ^ E))
    (ϖ g h : R)
    (hϖ : ι (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) ϖ) = UVCrossingModel.const (π ^ E) π)
    (hg : Ideal.map ι (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (Ideal.span {ϖ, g}))
      = Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E)})
    (hh : Ideal.map ι (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (Ideal.span {ϖ, h}))
      = Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.V (π ^ E)}) :
    ∃ g' h' w : R, IsUnit w ∧ g' * h' = ϖ ^ E * w ∧
      IsLocalRing.maximalIdeal R = Ideal.span {ϖ, g', h'} ∧
      (Ideal.span {ϖ, g'}).IsPrime ∧ (Ideal.span {ϖ, h'}).IsPrime ∧
      h' ∉ Ideal.span {ϖ, g'} ∧ g' ∉ Ideal.span {ϖ, h'} ∧
      Ideal.span {ϖ, g'} = Ideal.span {ϖ, g} ∧ Ideal.span {ϖ, h'} = Ideal.span {ϖ, h} := by
  classical

  set Rh := AdicCompletion (IsLocalRing.maximalIdeal R) R with hRh
  set πM := UVCrossingModel.const (π ^ E) π with hπMdef
  set UU := UVCrossingModel.U (π ^ E) with hUUdef
  set VV := UVCrossingModel.V (π ^ E) with hVVdef
  set φ : R →+* UVCrossingModel W (π ^ E) := ι.toRingHom.comp (algebraMap R Rh) with hφdef
  have hφ : ∀ r, φ r = ι (algebraMap R Rh r) := fun r => rfl
  have hmapφ : ∀ I : Ideal R, I.map φ = Ideal.map ι (I.map (algebraMap R Rh)) := by
    intro I; rw [hφdef, ← Ideal.map_map]; rfl

  have hιmem : ∀ (X : Ideal Rh) (y : Rh), y ∈ X ↔ ι y ∈ Ideal.map ι X := by
    intro X y
    rw [← Ideal.comap_symm, Ideal.mem_comap]
    show y ∈ X ↔ ι.symm (ι y) ∈ X
    rw [ι.symm_apply_apply]
  have hιmem' : ∀ (X : Ideal Rh) (z : UVCrossingModel W (π ^ E)), z ∈ Ideal.map ι X ↔ ι.symm z ∈ X := by
    intro X z
    rw [hιmem X, ι.apply_symm_apply]

  have hcomap : ∀ I : Ideal R, (I.map φ).comap φ = I := by
    intro I
    ext r
    rw [Ideal.mem_comap, hmapφ, hφ, ← hιmem, ← Ideal.mem_comap, IsLocalRing.comap_map_adicCompletion_eq]
  have hmem_of_map : ∀ (I : Ideal R) (r : R), φ r ∈ I.map φ → r ∈ I := by
    intro I r hr; rw [← hcomap I]; exact hr

  obtain ⟨hMdom, hMloc, -⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE
  obtain ⟨hprU, hVnot⟩ := isPrime_span_pi_U_and π hπ E hE
  obtain ⟨hprV, hUnot⟩ := isPrime_span_pi_V_and π hπ E hE
  simp only [← hπMdef, ← hUUdef, ← hVVdef] at hprU hVnot hprV hUnot
  have hUV : UU * VV = πM ^ E := U_mul_V_eq_pow π E
  have hVU : VV * UU = πM ^ E := by rw [mul_comm, hUV]
  have hU0 : UU ≠ 0 := by
    intro h0; apply hUnot; rw [h0]; exact zero_mem _
  have hV0 : VV ≠ 0 := by
    intro h0; apply hVnot; rw [h0]; exact zero_mem _
  have hπE0 : πM ^ E ≠ 0 := by rw [← hUV]; exact mul_ne_zero hU0 hV0

  set P₁ : Ideal R := Ideal.span {ϖ, g} with hP₁def
  set P₂ : Ideal R := Ideal.span {ϖ, h} with hP₂def
  have hP₁ : P₁.map φ = Ideal.span {πM, UU} := by rw [hmapφ]; exact hg
  have hP₂ : P₂.map φ = Ideal.span {πM, VV} := by rw [hmapφ]; exact hh
  have hP₁pr : P₁.IsPrime := by
    rw [← hcomap P₁, hP₁]; haveI := hprU; exact Ideal.comap_isPrime φ _
  have hP₂pr : P₂.IsPrime := by
    rw [← hcomap P₂, hP₂]; haveI := hprV; exact Ideal.comap_isPrime φ _
  have hφϖ : φ ϖ = πM := hϖ

  haveI : Module.Flat R Rh := AdicCompletion.flat_of_isNoetherian _

  have construct : ∀ (Pa Pb : Ideal R) (A B : UVCrossingModel W (π ^ E)),
      Pa.map φ = Ideal.span {πM, A} → Pb.map φ = Ideal.span {πM, B} → A * B = πM ^ E →
      (∀ f, (∀ s ∈ (Ideal.span {πM, B}) ^ (E - 1), f * s ∈ (Ideal.span {πM, A}) ^ E) → f ∈ Ideal.span {A}) →
      ∃ (a : R) (u : UVCrossingModel W (π ^ E)), IsUnit u ∧ φ a = A * u := by
    intro Pa Pb A B hPa hPb hAB hcolon
    set J : Ideal R := Submodule.colon (Pa ^ E) ((Pb ^ (E - 1) : Ideal R) : Set R) with hJdef
    have hJmap : J.map φ = Ideal.span {A} := by
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        rw [Ideal.mem_comap]
        apply hcolon
        intro s hs
        rw [← hPb, ← Ideal.map_pow] at hs
        rw [← hPa, ← Ideal.map_pow]
        have hle : Ideal.span {r} * Pb ^ (E - 1) ≤ Pa ^ E := by
          rw [Ideal.span_singleton_mul_le_iff]
          intro z hz
          exact (Submodule.mem_colon.mp hr) z hz
        have hle' : Ideal.span {φ r} * (Pb ^ (E - 1)).map φ ≤ (Pa ^ E).map φ := by
          have : Ideal.span {φ r} = (Ideal.span {r}).map φ := by
            rw [Ideal.map_span, Set.image_singleton]
          rw [this, ← Ideal.map_mul]
          exact Ideal.map_mono hle
        exact hle' (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hs)
      · rw [Ideal.span_singleton_le_iff_mem, hmapφ, hιmem', hJdef,
          Ideal.map_colon_eq_colon_map_of_flat (S := Rh) (Pa ^ E) (Pb ^ (E - 1)) (IsNoetherian.noetherian _),
          Submodule.mem_colon]
        intro t ht
        rw [smul_eq_mul, hιmem, map_mul, ι.apply_symm_apply, ← hmapφ, Ideal.map_pow, hPa]
        have ht' : ι t ∈ (Ideal.span {πM, B}) ^ (E - 1) := by
          rw [← hPb, ← Ideal.map_pow, hmapφ, ← hιmem]; exact ht
        exact mul_mem_pow_of_mem π E hE A B hAB (ι t) ht'

    have hJmap' : J.map (algebraMap R Rh) = Ideal.span {ι.symm A} := by
      have : Ideal.map ι (J.map (algebraMap R Rh)) = Ideal.map ι (Ideal.span {ι.symm A}) := by
        rw [← hmapφ, hJmap, Ideal.map_span, Set.image_singleton, ι.apply_symm_apply]
      have hinj : Function.Injective (Ideal.map ι : Ideal Rh → Ideal (UVCrossingModel W (π ^ E))) := by
        intro X Y hXY
        ext y
        rw [hιmem X, hιmem Y, hXY]
      exact hinj this
    have hJprinc : J.IsPrincipal :=
      IsLocalRing.isPrincipal_of_isPrincipal_map_adicCompletion J (by rw [hJmap']; exact ⟨⟨ι.symm A, rfl⟩⟩)
    obtain ⟨a, ha⟩ := hJprinc.principal
    refine ⟨a, ?_⟩
    have hspan : Ideal.span {φ a} = Ideal.span {A} := by
      rw [← hJmap, show J = Ideal.span {a} from ha, Ideal.map_span, Set.image_singleton]
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan.symm
    exact ⟨u, u.isUnit, hu.symm⟩

  obtain ⟨eU, heUV, heUU, heUC⟩ :=
    ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (π ^ E)
  obtain ⟨eV, heVU, heVV, heVC⟩ :=
    ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries (π ^ E)
  obtain ⟨g', u₁, hu₁, hg'⟩ := construct P₁ P₂ UU VV hP₁ hP₂ hUV
    (fun f hf => mem_span_of_forall_mul_mem π E UU VV hUV eU heUV f hf)
  obtain ⟨h', u₂, hu₂, hh'⟩ := construct P₂ P₁ VV UU hP₂ hP₁ hVU
    (fun f hf => mem_span_of_forall_mul_mem π E VV UU hVU eV heVU f hf)

  have hprod : φ (g' * h') = φ (ϖ ^ E) * (u₁ * u₂) := by
    rw [map_mul, hg', hh', map_pow, hφϖ, ← hUV]; ring
  have hmemw : g' * h' ∈ Ideal.span {ϖ ^ E} := by
    apply hmem_of_map
    rw [hprod, Ideal.map_span, Set.image_singleton]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmemw
  have hφw : φ w = u₁ * u₂ := by
    have h1 : φ (ϖ ^ E) * φ w = φ (ϖ ^ E) * (u₁ * u₂) := by
      rw [← map_mul, mul_comm, hw, hprod]
    have h2 : φ (ϖ ^ E) ≠ 0 := by rw [map_pow, hφϖ]; exact hπE0
    exact mul_left_cancel₀ h2 h1
  have hwunit : IsUnit w := by
    have h1 : IsUnit (φ w) := by rw [hφw]; exact hu₁.mul hu₂
    rw [hφ] at h1
    have h2 : IsUnit (algebraMap R Rh w) := by simpa using h1.map ι.symm
    exact AdicCompletion.isUnit_of_isUnit_algebraMap h2

  have hspan_g : Ideal.span {ϖ, g'} = P₁ := by
    rw [← hcomap (Ideal.span {ϖ, g'}), ← hcomap P₁, hP₁]
    congr 1
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hφϖ, hg', span_pair_unit _ _ _ hu₁]
  have hspan_h : Ideal.span {ϖ, h'} = P₂ := by
    rw [← hcomap (Ideal.span {ϖ, h'}), ← hcomap P₂, hP₂]
    congr 1
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hφϖ, hh', span_pair_unit _ _ _ hu₂]

  have hh'not : h' ∉ Ideal.span {ϖ, g'} := by
    rw [hspan_g]
    intro hmem
    have h1 : φ h' ∈ P₁.map φ := Ideal.mem_map_of_mem _ hmem
    rw [hP₁, hh'] at h1
    rcases hprU.mem_or_mem h1 with h2 | h2
    · exact hVnot h2
    · exact hprU.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu₂)
  have hg'not : g' ∉ Ideal.span {ϖ, h'} := by
    rw [hspan_h]
    intro hmem
    have h1 : φ g' ∈ P₂.map φ := Ideal.mem_map_of_mem _ hmem
    rw [hP₂, hg'] at h1
    rcases hprV.mem_or_mem h1 with h2 | h2
    · exact hUnot h2
    · exact hprV.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu₁)

  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ, g', h'} := by
    apply le_antisymm
    · intro r hr
      apply hmem_of_map
      have hnu : ¬ IsUnit (φ r) := by
        intro hu
        rw [hφ] at hu
        have h2 : IsUnit (algebraMap R Rh r) := by simpa using hu.map ι.symm
        exact (IsLocalRing.mem_maximalIdeal r).mp hr (AdicCompletion.isUnit_of_isUnit_algebraMap h2)
      have h3 := mem_span_of_not_isUnit π hπ E (φ r) hnu
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hφϖ, hg', hh',
        span_triple_units _ _ _ _ _ hu₁ hu₂]
      exact h3
    · rw [Ideal.span_le]
      have hmemM : ∀ x : R, φ x ∈ Ideal.span {πM, UU} → x ∈ IsLocalRing.maximalIdeal R := by
        intro x hx
        rw [IsLocalRing.mem_maximalIdeal]
        intro hxu
        exact hprU.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (hxu.map φ))
      have hmemM' : ∀ x : R, φ x ∈ Ideal.span {πM, VV} → x ∈ IsLocalRing.maximalIdeal R := by
        intro x hx
        rw [IsLocalRing.mem_maximalIdeal]
        intro hxu
        exact hprV.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (hxu.map φ))
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe]
      rcases hx with hx | hx | hx
      · rw [hx]; exact hmemM ϖ (by rw [hφϖ]; exact Ideal.subset_span (by simp))
      · rw [hx]; exact hmemM g' (by rw [hg']; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      · rw [hx]; exact hmemM' h' (by rw [hh']; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  refine ⟨g', h', w, hwunit, (by rw [← hw, mul_comm]), hmax, ?_, ?_, hh'not, hg'not, hspan_g, hspan_h⟩
  · rw [hspan_g]; exact hP₁pr
  · rw [hspan_h]; exact hP₂pr

end S_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
end P2MW
export P2MW.S_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel (solution)
