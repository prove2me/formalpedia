-- Prove2me | solution 1 for LanglandsTunnell.CubicLambda.zetaEulerPoly_eq_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a5832a7e-6a10-58d9-9f24-d3ba1b487dda

import Definitions.Def_LanglandsTunnell_CubicLambda
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda Polynomial
open scoped Pointwise

namespace ZetaEulerOfResolvent

section Eval

variable (F : Type) [Field F] [Algebra (𝓞 ℚ) (𝓞 F)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 F)]
variable (p : HeightOneSpectrum (𝓞 ℚ)) (g : HeightOneSpectrum (𝓞 F) → ℂ)

private theorem inducedFactor_eq_of_under {𝔓 : HeightOneSpectrum (𝓞 F)} (h : 𝔓.under (𝓞 ℚ) = p) :
    inducedFactor ℚ g 𝔓 = C 1 - C (g 𝔓) * X ^ (p.asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  unfold inducedFactor
  rw [h]

private theorem inducedEulerPoly_eq_of_fibre_eq_singleton {a : HeightOneSpectrum (𝓞 F)}
    (hfib : primeFibre ℚ F p = {a}) :
    inducedEulerPoly ℚ g p = inducedFactor ℚ g a := by
  unfold inducedEulerPoly
  rw [hfib]
  exact finprod_mem_singleton

private theorem inducedEulerPoly_eq_of_fibre_eq_pair {a b : HeightOneSpectrum (𝓞 F)} (hab : a ≠ b)
    (hfib : primeFibre ℚ F p = {a, b}) :
    inducedEulerPoly ℚ g p = inducedFactor ℚ g a * inducedFactor ℚ g b := by
  unfold inducedEulerPoly
  rw [hfib]
  exact finprod_mem_pair hab

private theorem inducedEulerPoly_eq_of_fibre_eq_triple {a b c : HeightOneSpectrum (𝓞 F)} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hfib : primeFibre ℚ F p = {a, b, c}) :
    inducedEulerPoly ℚ g p = inducedFactor ℚ g a * (inducedFactor ℚ g b * inducedFactor ℚ g c) := by
  unfold inducedEulerPoly
  rw [hfib, finprod_mem_insert _ (by simp [hab, hac]) (Set.toFinite _), finprod_mem_pair hbc]

private theorem zetaEulerPoly_eq_induced_one [NumberField F] :
    zetaEulerPoly F p = inducedEulerPoly ℚ (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) p :=
  rfl

private theorem mem_fibre_of_fibre_eq {S : Set (HeightOneSpectrum (𝓞 F))} (hfib : primeFibre ℚ F p = S)
    {a : HeightOneSpectrum (𝓞 F)} (ha : a ∈ S) : a.under (𝓞 ℚ) = p := by
  have : a ∈ primeFibre ℚ F p := hfib ▸ ha
  exact (mem_primeFibre ℚ p a).mp this

end Eval

private theorem cube_identity {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    ((1 : ℂ[X]) - X) * ((1 - C ζ * X) * (1 - C ζ⁻¹ * X)) = 1 - X ^ 3 := by
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hsum : ζ ^ 2 + ζ + 1 = 0 := by
    have h := hζ.geom_sum_eq_zero (by norm_num : 1 < 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
    linear_combination h
  have hinv : ζ⁻¹ = ζ ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc ζ * ζ ^ 2 = ζ ^ 3 := by ring
      _ = 1 := h3
  have hC : C ζ ^ 2 + C ζ + 1 = (0 : ℂ[X]) := by
    have h := congrArg (C : ℂ →+* ℂ[X]) hsum
    simpa only [map_add, map_pow, map_one, map_zero] using h
  rw [hinv, map_pow]
  linear_combination (-X + C ζ * X ^ 2 - (C ζ - 1) * X ^ 3) * hC

section InstanceUniqueness

private theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

private theorem exists_algHom_of_ringOfIntegers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra (𝓞 F) (𝓞 E)] :
    ∃ φ : F →ₐ[ℚ] E, ∀ x : 𝓞 F, φ (algebraMap (𝓞 F) F x) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) x) := by
  set g : 𝓞 F →+* E := (algebraMap (𝓞 E) E).comp (algebraMap (𝓞 F) (𝓞 E)) with hg_def
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hI : (Ideal.span {x} : Ideal (𝓞 F)) ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hx0
    have hmem : ((Ideal.absNorm (Ideal.span {x} : Ideal (𝓞 F)) : ℕ) : 𝓞 F) ∈ (Ideal.span {x} : Ideal (𝓞 F)) :=
      Ideal.absNorm_mem _
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    have hN : (Ideal.absNorm (Ideal.span {x} : Ideal (𝓞 F)) : ℕ) ≠ 0 :=
      (Ideal.absNorm_eq_zero_iff.not).mpr hI
    have h1 : g (((Ideal.absNorm (Ideal.span {x} : Ideal (𝓞 F)) : ℕ) : 𝓞 F)) = 0 := by
      rw [← hy, map_mul, hx, mul_zero]
    rw [map_natCast] at h1
    exact hN (Nat.cast_eq_zero.mp h1)
  refine ⟨(IsFractionRing.lift hg).toRatAlgHom, fun x => ?_⟩
  simp [RingHom.toRatAlgHom, IsFractionRing.lift_algebraMap, hg_def]

private theorem algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X] (i : Algebra (𝓞 ℚ) (𝓞 X)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (NumberField.inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun
      (ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
        (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ X))) r

end InstanceUniqueness

section Closing

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]

private theorem normal_of_fieldRange (φ : K →ₐ[ℚ] E) [Normal ℚ φ.fieldRange] : Normal ℚ K := by
  have hr : φ.range = φ.fieldRange.toSubalgebra := by
    ext y
    simp [AlgHom.mem_range]
  have e : φ.fieldRange ≃ₐ[ℚ] K :=
    ((AlgEquiv.ofInjectiveField φ).trans (Subalgebra.equivOfEq _ _ hr)).symm
  exact Normal.of_algEquiv e

private theorem not_normal_fixingSubgroup [IsGalois ℚ E] (φ : K →ₐ[ℚ] E) (hKn : ¬ Normal ℚ K) :
    ¬ φ.fieldRange.fixingSubgroup.Normal := by
  intro hN
  haveI : IsGalois ℚ φ.fieldRange := (InfiniteGalois.normal_iff_isGalois φ.fieldRange).mp hN
  exact hKn (normal_of_fieldRange φ)

end Closing

section Combinatorics

variable {α : Type} {s : Set α} {g : α → ℕ}

private theorem finsum_mem_eq_ncard_mul (hs : s.Finite) {m : ℕ} (hg : ∀ x ∈ s, g x = m) :
    ∑ᶠ x ∈ s, g x = s.ncard * m := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs,
    Finset.sum_congr rfl (fun x hx => hg x (hs.mem_toFinset.mp hx)), Finset.sum_const, smul_eq_mul,
    Set.ncard_eq_toFinset_card s hs]

private theorem le_finsum_mem_of_mem (hs : s.Finite) {x : α} (hx : x ∈ s) : g x ≤ ∑ᶠ y ∈ s, g y := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hs.mem_toFinset.mpr hx)

private theorem eq_pair_of_finsum_mem_eq_three (hs : s.Finite) (h3 : ∑ᶠ x ∈ s, g x = 3)
    (h12 : ∀ x ∈ s, g x = 1 ∨ g x = 2) {b : α} (hb : b ∈ s) (hgb : g b = 2) :
    ∃ a, a ≠ b ∧ s = {a, b} ∧ g a = 1 := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hs] at h3
  have hbt : b ∈ hs.toFinset := hs.mem_toFinset.mpr hb
  rw [← Finset.add_sum_erase _ _ hbt, hgb] at h3
  have hrest : ∑ x ∈ hs.toFinset.erase b, g x = 1 := by omega
  have hpos : ∀ x ∈ hs.toFinset.erase b, 1 ≤ g x := fun x hx => by
    rcases h12 x (hs.mem_toFinset.mp (Finset.mem_of_mem_erase hx)) with h | h <;> omega
  have hcard : (hs.toFinset.erase b).card ≤ 1 := by
    have h := Finset.card_nsmul_le_sum (hs.toFinset.erase b) g 1 hpos
    rw [hrest, smul_eq_mul, mul_one] at h
    exact h
  have hne : (hs.toFinset.erase b).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hrest
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (le_antisymm hcard hne.card_pos)
  have hat : a ∈ hs.toFinset.erase b := by
    rw [ha]
    exact Finset.mem_singleton_self a
  refine ⟨a, Finset.ne_of_mem_erase hat, ?_, ?_⟩
  · have ht : hs.toFinset = {a, b} := by
      rw [← Finset.insert_erase hbt, ha, Finset.pair_comm]
    rw [← hs.coe_toFinset, ht, Finset.coe_pair]
  · rw [ha, Finset.sum_singleton] at hrest
    exact hrest

end Combinatorics

section Counting

variable (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 ℚ))

private theorem asIdeal_mem_primesOver_of_mem_primeFibre {𝔓 : HeightOneSpectrum (𝓞 F)} (h : 𝔓 ∈ primeFibre ℚ F p) :
    𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 F) := by
  rw [mem_primeFibre] at h
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

private theorem image_asIdeal_primeFibre :
    HeightOneSpectrum.asIdeal '' primeFibre ℚ F p = p.asIdeal.primesOver (𝓞 F) := by
  ext Q
  constructor
  · rintro ⟨𝔓, h𝔓, rfl⟩
    exact asIdeal_mem_primesOver_of_mem_primeFibre F p h𝔓
  · intro hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p.asIdeal := hQ.2
    refine ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ⟩, ?_, rfl⟩
    rw [mem_primeFibre]
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def Q p.asIdeal).symm

private theorem primeFibre_finite : (primeFibre ℚ F p).Finite := by
  have hfin : (p.asIdeal.primesOver (𝓞 F)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)
  rw [← image_asIdeal_primeFibre F p] at hfin
  exact hfin.of_finite_image HeightOneSpectrum.asIdeal_injective.injOn

private theorem ncard_primeFibre : (primeFibre ℚ F p).ncard = (p.asIdeal.primesOver (𝓞 F)).ncard := by
  rw [← image_asIdeal_primeFibre F p, Set.ncard_image_of_injective _ HeightOneSpectrum.asIdeal_injective]

private theorem finsum_fibre_ramificationIdx_mul_inertiaDeg :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal =
      Module.finrank ℚ F := by
  calc ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal
      = ∑ᶠ Q ∈ HeightOneSpectrum.asIdeal '' primeFibre ℚ F p,
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q :=
        (finsum_mem_image (f := fun Q : Ideal (𝓞 F) => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q)
          HeightOneSpectrum.asIdeal_injective.injOn).symm
    _ = ∑ᶠ Q ∈ p.asIdeal.primesOver (𝓞 F), p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [image_asIdeal_primeFibre]
    _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 F),
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [← IsDedekindDomain.coe_primesOverFinset p.ne_bot (𝓞 F), finsum_mem_coe_finset]
    _ = Module.finrank ℚ F := Ideal.sum_ramification_inertia (𝓞 F) ℚ F p.ne_bot

private theorem finsum_fibre_inertiaDeg_of_unramified
    (hp : ∀ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = Module.finrank ℚ F := by
  rw [← finsum_fibre_ramificationIdx_mul_inertiaDeg F p]
  exact finsum_mem_congr rfl fun 𝔓 h𝔓 => by rw [hp 𝔓 h𝔓, one_mul]

end Counting

section InstanceTransfer

private theorem exists_algHom_algebra_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    (j : Algebra (𝓞 F) (𝓞 E)) :
    ∃ φ : F →ₐ[ℚ] E, j = @NumberField.inst_ringOfIntegersAlgebra F E _ _ φ.toAlgebra := by
  obtain ⟨φ, hφ⟩ := @exists_algHom_of_ringOfIntegers F E _ _ _ _ j
  refine ⟨φ, ?_⟩
  letI : Algebra F E := φ.toAlgebra
  refine Algebra.algebra_ext j _ fun x => ?_
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ← hφ x]
  exact (NumberField.RingOfIntegers.mapRingHom_apply (algebraMap F E) x).symm

end InstanceTransfer

section Relative

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (p : HeightOneSpectrum (𝓞 ℚ))

omit [IsGalois ℚ E] in
private theorem mul_finrank_top (X : Type) [Field X] [NumberField X] [Algebra X E] [IsScalarTower ℚ X E] {d n : ℕ}
    (hX : Module.finrank ℚ X = d) (hE : Module.finrank ℚ E = n) : d * Module.finrank X E = n := by
  rw [← hX, ← hE]
  exact Module.finrank_mul_finrank ℚ X E

private theorem relative_data {X : Type} [Field X] [NumberField X] [Algebra X E] [IsScalarTower ℚ X E]
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    {𝔓 : HeightOneSpectrum (𝓞 X)} (h𝔓 : 𝔓 ∈ primeFibre ℚ X p) :
    p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 ∧
      ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 X) = 𝔓 ∧
        p.asIdeal.inertiaDeg' 𝔓.asIdeal * 𝔓.asIdeal.inertiaDeg' 𝔔.asIdeal = p.asIdeal.inertiaDegIn (𝓞 E) ∧
        (𝔓.asIdeal.primesOver (𝓞 E)).ncard * 𝔓.asIdeal.inertiaDeg' 𝔔.asIdeal = Module.finrank X E := by
  haveI hPp : 𝔓.asIdeal.LiesOver p.asIdeal := (asIdeal_mem_primesOver_of_mem_primeFibre X p h𝔓).2
  obtain ⟨𝔔, h𝔔⟩ : ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.asIdeal ∈ 𝔓.asIdeal.primesOver (𝓞 E) := by
    obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) 𝔓.asIdeal
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver 𝔓.ne_bot hQ⟩, hQ⟩
  haveI hQP : 𝔔.asIdeal.LiesOver 𝔓.asIdeal := h𝔔.2
  haveI hQp : 𝔔.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.trans 𝔔.asIdeal 𝔓.asIdeal p.asIdeal
  have h𝔔X : 𝔔.under (𝓞 X) = 𝔓 := HeightOneSpectrum.ext (Ideal.over_def 𝔔.asIdeal 𝔓.asIdeal).symm
  have h𝔔ℚ : 𝔔.under (𝓞 ℚ) = p := HeightOneSpectrum.ext (Ideal.over_def 𝔔.asIdeal p.asIdeal).symm
  have he : p.asIdeal.ramificationIdx' 𝔓.asIdeal * 𝔓.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 := by
    rw [← Ideal.ramificationIdx_algebra_tower' p.asIdeal 𝔓.asIdeal 𝔔.asIdeal]
    exact hp 𝔔 h𝔔ℚ
  refine ⟨Nat.eq_one_of_mul_eq_one_right he, 𝔔, h𝔔X, ?_, ?_⟩
  · rw [Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal 𝔔.asIdeal (E ≃ₐ[ℚ] E),
      ← Ideal.inertiaDeg'_eq_inertiaDeg p.asIdeal 𝔔.asIdeal,
      Ideal.inertiaDeg_algebra_tower p.asIdeal 𝔓.asIdeal 𝔔.asIdeal]
  · haveI : IsGalois X E := IsGalois.tower_top_of_isGalois ℚ X E
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔓.asIdeal (𝓞 E) (E ≃ₐ[X] E)
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔓.asIdeal 𝔔.asIdeal (E ≃ₐ[X] E),
      ← Ideal.ramificationIdx'_eq_ramificationIdx 𝔓.asIdeal 𝔔.asIdeal 𝔓.ne_bot,
      Nat.eq_one_of_mul_eq_one_left he, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg 𝔓.asIdeal 𝔔.asIdeal (E ≃ₐ[X] E),
      ← Ideal.inertiaDeg'_eq_inertiaDeg 𝔓.asIdeal 𝔔.asIdeal, IsGalois.card_aut_eq_finrank X E] at h

private theorem inertiaDegIn_dvd_finrank : p.asIdeal.inertiaDegIn (𝓞 E) ∣ Module.finrank ℚ E := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p.asIdeal (𝓞 E) (E ≃ₐ[ℚ] E)
  rw [IsGalois.card_aut_eq_finrank ℚ E, ← mul_assoc] at h
  exact Dvd.intro_left _ h

private theorem card_stabilizer_eq_inertiaDegIn
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    {𝔔 : HeightOneSpectrum (𝓞 E)} (h𝔔 : 𝔔 ∈ primeFibre ℚ E p) :
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) 𝔔.asIdeal) = p.asIdeal.inertiaDegIn (𝓞 E) := by
  haveI : 𝔔.asIdeal.LiesOver p.asIdeal := (asIdeal_mem_primesOver_of_mem_primeFibre E p h𝔔).2
  letI := Ideal.Quotient.field p.asIdeal
  letI := Ideal.Quotient.field 𝔔.asIdeal
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) p.asIdeal 𝔔.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal 𝔔.asIdeal (E ≃ₐ[ℚ] E),
      ← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal 𝔔.asIdeal p.ne_bot, hp 𝔔 ((mem_primeFibre ℚ p 𝔔).mp h𝔔),
    one_mul]

variable (K : Type) [Field K] [NumberField K] [Algebra K E] [IsScalarTower ℚ K E]

private noncomputable def restrictHom : (E ≃ₐ[K] E) →* (E ≃ₐ[ℚ] E) where
  toFun τ := AlgEquiv.restrictScalars (R := ℚ) τ
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

omit [IsGalois ℚ E] in
private theorem restrictHom_smul (τ : E ≃ₐ[K] E) (I : Ideal (𝓞 E)) : restrictHom K τ • I = τ • I := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  exact Iff.rfl

omit [IsGalois ℚ E] in
private theorem range_restrictHom :
    (restrictHom K (E := E)).range = (IsScalarTower.toAlgHom ℚ K E).fieldRange.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun k => hσ _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩),
      AlgEquiv.ext fun _ => rfl⟩

private theorem card_range_restrictHom (hK : Module.finrank ℚ K = 3) (hE : Module.finrank ℚ E = 6) :
    Nat.card (restrictHom K (E := E)).range = 2 := by
  haveI : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have hinj : Function.Injective (restrictHom K (E := E)) := fun _ _ h =>
    AlgEquiv.restrictScalars_injective (R := ℚ) h
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, IsGalois.card_aut_eq_finrank K E]
  have h := mul_finrank_top K hK hE
  omega

private theorem range_restrictHom_eq_stabilizer (hK : Module.finrank ℚ K = 3) (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    (h2 : p.asIdeal.inertiaDegIn (𝓞 E) = 2)
    (hall : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 1)
    {Q : Ideal (𝓞 E)} (hQ : Q ∈ p.asIdeal.primesOver (𝓞 E)) :
    (restrictHom K (E := E)).range = MulAction.stabilizer (E ≃ₐ[ℚ] E) Q := by
  obtain ⟨𝔔, h𝔔, rfl⟩ : Q ∈ HeightOneSpectrum.asIdeal '' primeFibre ℚ E p := by
    rw [image_asIdeal_primeFibre]
    exact hQ
  have h𝔓 : 𝔔.under (𝓞 K) ∈ primeFibre ℚ K p := by
    rw [mem_primeFibre, ← (mem_primeFibre ℚ p 𝔔).mp h𝔔]
    exact HeightOneSpectrum.ext (Ideal.under_under 𝔔.asIdeal)
  obtain ⟨-, 𝔔', -, hf, hn⟩ := relative_data p hp h𝔓
  rw [hall _ h𝔓, one_mul, h2] at hf
  have hEK : Module.finrank K E = 2 := by
    have h := mul_finrank_top K hK hE
    omega
  rw [hf, hEK] at hn
  have hone : ((𝔔.under (𝓞 K)).asIdeal.primesOver (𝓞 E)).ncard = 1 := by omega
  obtain ⟨Q₀, hQ₀⟩ := Set.ncard_eq_one.mp hone
  haveI : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  haveI : 𝔔.asIdeal.LiesOver (𝔔.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have horb := Algebra.IsInvariant.orbit_eq_primesOver (A := 𝓞 K) (B := 𝓞 E) (G := E ≃ₐ[K] E)
    (𝔔.under (𝓞 K)).asIdeal 𝔔.asIdeal
  have hle : (restrictHom K (E := E)).range ≤ MulAction.stabilizer (E ≃ₐ[ℚ] E) 𝔔.asIdeal := by
    rintro σ ⟨τ, rfl⟩
    rw [MulAction.mem_stabilizer_iff, restrictHom_smul]
    have h1 : τ • 𝔔.asIdeal ∈ (𝔔.under (𝓞 K)).asIdeal.primesOver (𝓞 E) := by
      rw [← horb]
      exact MulAction.mem_orbit 𝔔.asIdeal τ
    have h0 : 𝔔.asIdeal ∈ (𝔔.under (𝓞 K)).asIdeal.primesOver (𝓞 E) := by
      rw [← horb]
      exact MulAction.mem_orbit_self 𝔔.asIdeal
    rw [hQ₀, Set.mem_singleton_iff] at h1 h0
    exact h1.trans h0.symm
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [card_stabilizer_eq_inertiaDegIn p hp h𝔔, h2, card_range_restrictHom K hK hE]

variable (L : Type) [Field L] [NumberField L] [Algebra L E] [IsScalarTower ℚ L E]

private theorem inertiaDegIn_ne_six (hKn : ¬ Normal ℚ K) (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1) :
    p.asIdeal.inertiaDegIn (𝓞 E) ≠ 6 := by
  intro h6
  obtain ⟨𝔔, h𝔔⟩ : (primeFibre ℚ E p).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    rw [ncard_primeFibre]
    exact IsDedekindDomain.primesOver_ncard_ne_zero p.asIdeal (𝓞 E))
  have h𝔔p : 𝔔.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p 𝔔).mp h𝔔
  haveI : 𝔔.asIdeal.LiesOver p.asIdeal := (asIdeal_mem_primesOver_of_mem_primeFibre E p h𝔔).2
  letI := Ideal.Quotient.field p.asIdeal
  letI := Ideal.Quotient.field 𝔔.asIdeal

  have hstab : Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) 𝔔.asIdeal) = Nat.card (E ≃ₐ[ℚ] E) := by
    rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) p.asIdeal 𝔔.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal 𝔔.asIdeal (E ≃ₐ[ℚ] E),
      ← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal 𝔔.asIdeal p.ne_bot, hp 𝔔 h𝔔p, one_mul, h6,
      IsGalois.card_aut_eq_finrank ℚ E, hE]
  have hin : Nat.card (𝔔.asIdeal.inertia (E ≃ₐ[ℚ] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) p.asIdeal 𝔔.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal 𝔔.asIdeal (E ≃ₐ[ℚ] E),
      ← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal 𝔔.asIdeal p.ne_bot]
    exact hp 𝔔 h𝔔p

  have hinj : Function.Injective (Ideal.Quotient.stabilizerHom 𝔔.asIdeal p.asIdeal (E ≃ₐ[ℚ] E)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _),
      Ideal.Quotient.map_ker_stabilizer_subtype, Subgroup.eq_bot_of_card_eq _ hin]
  have e : MulAction.stabilizer (E ≃ₐ[ℚ] E) 𝔔.asIdeal ≃*
      ((𝓞 E ⧸ 𝔔.asIdeal) ≃ₐ[𝓞 ℚ ⧸ p.asIdeal] (𝓞 E ⧸ 𝔔.asIdeal)) :=
    MulEquiv.ofBijective _ ⟨hinj, Ideal.Quotient.stabilizerHom_surjective (E ≃ₐ[ℚ] E) p.asIdeal 𝔔.asIdeal⟩
  have hcyc : IsCyclic (MulAction.stabilizer (E ≃ₐ[ℚ] E) 𝔔.asIdeal) := isCyclic_of_surjective e.symm e.symm.surjective
  rw [Subgroup.eq_top_of_card_eq _ hstab] at hcyc
  haveI : IsCyclic (E ≃ₐ[ℚ] E) :=
    isCyclic_of_surjective (Subgroup.topEquiv (G := E ≃ₐ[ℚ] E)) Subgroup.topEquiv.surjective

  exact not_normal_fixingSubgroup (IsScalarTower.toAlgHom ℚ K E) hKn (Subgroup.normal_of_isMulCommutative _)

private theorem exists_inertiaDeg_ne_one_of_inertiaDegIn_eq_two (hKn : ¬ Normal ℚ K) (hK : Module.finrank ℚ K = 3)
    (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    (h2 : p.asIdeal.inertiaDegIn (𝓞 E) = 2) :
    ∃ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 1 := by
  by_contra hcon
  have hall : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 1 := fun 𝔓 h𝔓 =>
    by_contra fun hne => hcon ⟨𝔓, h𝔓, hne⟩
  have hH : ∀ {Q : Ideal (𝓞 E)}, Q ∈ p.asIdeal.primesOver (𝓞 E) →
      (restrictHom K (E := E)).range = MulAction.stabilizer (E ≃ₐ[ℚ] E) Q :=
    fun hQ => range_restrictHom_eq_stabilizer p K hK hE hp h2 hall hQ
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) p.asIdeal
  haveI : Q.IsPrime := hQ.1
  haveI : Q.LiesOver p.asIdeal := hQ.2

  have hnormal : (restrictHom K (E := E)).range.Normal := by
    refine ⟨fun n hn σ => ?_⟩
    have hσQ : σ • Q ∈ p.asIdeal.primesOver (𝓞 E) := by
      rw [← Algebra.IsInvariant.orbit_eq_primesOver (A := 𝓞 ℚ) (B := 𝓞 E) (G := E ≃ₐ[ℚ] E) p.asIdeal Q]
      exact MulAction.mem_orbit Q σ
    have hmap : (restrictHom K (E := E)).range.map (MulAut.conj σ).toMonoidHom = (restrictHom K (E := E)).range :=
      calc (restrictHom K (E := E)).range.map (MulAut.conj σ).toMonoidHom
          = (MulAction.stabilizer (E ≃ₐ[ℚ] E) Q).map (MulAut.conj σ).toMonoidHom := by rw [hH hQ]
        _ = MulAction.stabilizer (E ≃ₐ[ℚ] E) (σ • Q) := (MulAction.stabilizer_smul_eq_stabilizer_map_conj σ Q).symm
        _ = (restrictHom K (E := E)).range := (hH hσQ).symm
    rw [← hmap]
    simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj σ).toMonoidHom hn
  rw [range_restrictHom] at hnormal
  exact not_normal_fixingSubgroup (IsScalarTower.toAlgHom ℚ K E) hKn hnormal

private theorem inertiaDegIn_cases_canonical (hKn : ¬ Normal ℚ K) (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1) :
    p.asIdeal.inertiaDegIn (𝓞 E) = 1 ∨ p.asIdeal.inertiaDegIn (𝓞 E) = 2 ∨ p.asIdeal.inertiaDegIn (𝓞 E) = 3 := by
  have hdvd := inertiaDegIn_dvd_finrank p (E := E)
  rw [hE] at hdvd
  have h6 := inertiaDegIn_ne_six p K hKn hE hp
  have hle : p.asIdeal.inertiaDegIn (𝓞 E) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  generalize p.asIdeal.inertiaDegIn (𝓞 E) = f at hdvd h6 hle ⊢
  interval_cases f <;> omega

private theorem shape_one_canonical (hK : Module.finrank ℚ K = 3) (hL : Module.finrank ℚ L = 2)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    (h1 : p.asIdeal.inertiaDegIn (𝓞 E) = 1) :
    (∃ a b c : HeightOneSpectrum (𝓞 K), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ primeFibre ℚ K p = {a, b, c} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' c.asIdeal = 1) ∧
    (∃ a b : HeightOneSpectrum (𝓞 L), a ≠ b ∧ primeFibre ℚ L p = {a, b} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 1 ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = a ∧ a.asIdeal.inertiaDeg' 𝔔.asIdeal = 1) ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = b ∧ b.asIdeal.inertiaDeg' 𝔔.asIdeal = 1)) := by
  have hKf : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 1 := fun 𝔓 h𝔓 => by
    obtain ⟨-, 𝔔, -, hf, -⟩ := relative_data p hp h𝔓
    rw [h1] at hf
    exact Nat.eq_one_of_mul_eq_one_right hf
  have hLf : ∀ 𝔮 ∈ primeFibre ℚ L p, p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 ∧
      ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = 𝔮 ∧ 𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal = 1 := fun 𝔮 h𝔮 => by
    obtain ⟨-, 𝔔, h𝔔, hf, -⟩ := relative_data p hp h𝔮
    rw [h1] at hf
    exact ⟨Nat.eq_one_of_mul_eq_one_right hf, 𝔔, h𝔔, Nat.eq_one_of_mul_eq_one_left hf⟩
  have hKcard : (primeFibre ℚ K p).ncard = 3 := by
    have h := finsum_fibre_inertiaDeg_of_unramified K p fun 𝔓 h𝔓 => (relative_data p hp h𝔓).1
    rwa [finsum_mem_eq_ncard_mul (g := fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal) (primeFibre_finite K p) hKf,
      mul_one, hK] at h
  have hLcard : (primeFibre ℚ L p).ncard = 2 := by
    have h := finsum_fibre_inertiaDeg_of_unramified L p fun 𝔮 h𝔮 => (relative_data p hp h𝔮).1
    rwa [finsum_mem_eq_ncard_mul (g := fun 𝔮 => p.asIdeal.inertiaDeg' 𝔮.asIdeal) (primeFibre_finite L p)
      (fun 𝔮 h𝔮 => (hLf 𝔮 h𝔮).1), mul_one, hL] at h
  obtain ⟨a, b, c, hab, hac, hbc, hfibK⟩ := Set.ncard_eq_three.mp hKcard
  obtain ⟨q, q', hqq', hfibL⟩ := Set.ncard_eq_two.mp hLcard
  have ha : a ∈ primeFibre ℚ K p := by rw [hfibK]; simp
  have hb : b ∈ primeFibre ℚ K p := by rw [hfibK]; simp
  have hc : c ∈ primeFibre ℚ K p := by rw [hfibK]; simp
  have hq : q ∈ primeFibre ℚ L p := by rw [hfibL]; simp
  have hq' : q' ∈ primeFibre ℚ L p := by rw [hfibL]; simp
  exact ⟨⟨a, b, c, hab, hac, hbc, hfibK, hKf a ha, hKf b hb, hKf c hc⟩,
    ⟨q, q', hqq', hfibL, (hLf q hq).1, (hLf q' hq').1, (hLf q hq).2, (hLf q' hq').2⟩⟩

private theorem shape_two_canonical (hKn : ¬ Normal ℚ K) (hK : Module.finrank ℚ K = 3) (hL : Module.finrank ℚ L = 2)
    (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    (h2 : p.asIdeal.inertiaDegIn (𝓞 E) = 2) :
    (∃ a b : HeightOneSpectrum (𝓞 K), a ≠ b ∧ primeFibre ℚ K p = {a, b} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 2) ∧
    (∃ a : HeightOneSpectrum (𝓞 L), primeFibre ℚ L p = {a} ∧ p.asIdeal.inertiaDeg' a.asIdeal = 2 ∧
      ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = a ∧ a.asIdeal.inertiaDeg' 𝔔.asIdeal = 1) := by
  have hEL : Module.finrank L E = 3 := by
    have h := mul_finrank_top L hL hE
    omega
  constructor
  ·
    have hK12 : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 1 ∨ p.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 :=
      fun 𝔓 h𝔓 => by
        obtain ⟨-, 𝔔, -, hf, -⟩ := relative_data p hp h𝔓
        rw [h2] at hf
        exact (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hf)
    have hsum : ∑ᶠ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by
      rw [finsum_fibre_inertiaDeg_of_unramified K p fun 𝔓 h𝔓 => (relative_data p hp h𝔓).1, hK]
    obtain ⟨b, hb, hfb⟩ := exists_inertiaDeg_ne_one_of_inertiaDegIn_eq_two p K hKn hK hE hp h2
    have hfb2 : p.asIdeal.inertiaDeg' b.asIdeal = 2 := (hK12 b hb).resolve_left hfb
    obtain ⟨a, hab, hfib, hfa⟩ :=
      eq_pair_of_finsum_mem_eq_three (g := fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal) (primeFibre_finite K p) hsum
        hK12 hb hfb2
    exact ⟨a, b, hab, hfib, hfa, hfb2⟩
  ·
    have hLf : ∀ 𝔮 ∈ primeFibre ℚ L p, p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 ∧
        ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = 𝔮 ∧ 𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal = 1 := fun 𝔮 h𝔮 => by
      obtain ⟨-, 𝔔, h𝔔, hf, hn⟩ := relative_data p hp h𝔮
      rw [h2] at hf
      rw [hEL] at hn
      have hrel : 𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal = 1 :=
        Nat.eq_one_of_dvd_one (Nat.dvd_sub (Dvd.intro_left _ hn) (Dvd.intro_left _ hf))
      rw [hrel, mul_one] at hf
      exact ⟨hf, 𝔔, h𝔔, hrel⟩
    have hLcard : (primeFibre ℚ L p).ncard = 1 := by
      have h := finsum_fibre_inertiaDeg_of_unramified L p fun 𝔮 h𝔮 => (relative_data p hp h𝔮).1
      rw [finsum_mem_eq_ncard_mul (g := fun 𝔮 => p.asIdeal.inertiaDeg' 𝔮.asIdeal) (primeFibre_finite L p)
        (fun 𝔮 h𝔮 => (hLf 𝔮 h𝔮).1), hL] at h
      omega
    obtain ⟨q, hfibL⟩ := Set.ncard_eq_one.mp hLcard
    have hq : q ∈ primeFibre ℚ L p := by rw [hfibL]; simp
    exact ⟨q, hfibL, (hLf q hq).1, (hLf q hq).2⟩

private theorem shape_three_canonical (hK : Module.finrank ℚ K = 3) (hL : Module.finrank ℚ L = 2)
    (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1)
    (h3 : p.asIdeal.inertiaDegIn (𝓞 E) = 3) :
    (∃ a : HeightOneSpectrum (𝓞 K), primeFibre ℚ K p = {a} ∧ p.asIdeal.inertiaDeg' a.asIdeal = 3) ∧
    (∃ a b : HeightOneSpectrum (𝓞 L), a ≠ b ∧ primeFibre ℚ L p = {a, b} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 1 ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = a ∧ a.asIdeal.inertiaDeg' 𝔔.asIdeal = 3) ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = b ∧ b.asIdeal.inertiaDeg' 𝔔.asIdeal = 3)) := by
  have hEK : Module.finrank K E = 2 := by
    have h := mul_finrank_top K hK hE
    omega
  constructor
  ·
    have hKf : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := fun 𝔓 h𝔓 => by
      obtain ⟨-, 𝔔, -, hf, hn⟩ := relative_data p hp h𝔓
      rw [h3] at hf
      rw [hEK] at hn
      have hrel : 𝔓.asIdeal.inertiaDeg' 𝔔.asIdeal = 1 :=
        Nat.eq_one_of_dvd_one (Nat.dvd_sub (Dvd.intro_left _ hf) (Dvd.intro_left _ hn))
      rwa [hrel, mul_one] at hf
    have hKcard : (primeFibre ℚ K p).ncard = 1 := by
      have h := finsum_fibre_inertiaDeg_of_unramified K p fun 𝔓 h𝔓 => (relative_data p hp h𝔓).1
      rw [finsum_mem_eq_ncard_mul (g := fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal) (primeFibre_finite K p) hKf,
        hK] at h
      omega
    obtain ⟨a, hfibK⟩ := Set.ncard_eq_one.mp hKcard
    have ha : a ∈ primeFibre ℚ K p := by rw [hfibK]; simp
    exact ⟨a, hfibK, hKf a ha⟩
  ·
    have hLe : ∀ 𝔮 ∈ primeFibre ℚ L p, p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 :=
      fun 𝔮 h𝔮 => (relative_data p hp h𝔮).1
    have hLf : ∀ 𝔮 ∈ primeFibre ℚ L p, p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 ∧
        ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = 𝔮 ∧ 𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal = 3 := fun 𝔮 h𝔮 => by
      obtain ⟨-, 𝔔, h𝔔, hf, -⟩ := relative_data p hp h𝔮
      rw [h3] at hf
      have hle : p.asIdeal.inertiaDeg' 𝔮.asIdeal ≤ 2 := by
        have h := le_finsum_mem_of_mem (g := fun 𝔮 => p.asIdeal.inertiaDeg' 𝔮.asIdeal) (primeFibre_finite L p) h𝔮
        rwa [finsum_fibre_inertiaDeg_of_unramified L p hLe, hL] at h
      obtain h0 | h1 | h2 : p.asIdeal.inertiaDeg' 𝔮.asIdeal = 0 ∨ p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 ∨
          p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 := by omega
      · rw [h0] at hf
        omega
      · rw [h1, one_mul] at hf
        exact ⟨h1, 𝔔, h𝔔, hf⟩
      · rw [h2] at hf
        omega
    have hLcard : (primeFibre ℚ L p).ncard = 2 := by
      have h := finsum_fibre_inertiaDeg_of_unramified L p hLe
      rwa [finsum_mem_eq_ncard_mul (g := fun 𝔮 => p.asIdeal.inertiaDeg' 𝔮.asIdeal) (primeFibre_finite L p)
        (fun 𝔮 h𝔮 => (hLf 𝔮 h𝔮).1), mul_one, hL] at h
    obtain ⟨q, q', hqq', hfibL⟩ := Set.ncard_eq_two.mp hLcard
    have hq : q ∈ primeFibre ℚ L p := by rw [hfibL]; simp
    have hq' : q' ∈ primeFibre ℚ L p := by rw [hfibL]; simp
    exact ⟨q, q', hqq', hfibL, (hLf q hq).1, (hLf q' hq').1, (hLf q hq).2, (hLf q' hq').2⟩

end Relative

section Types

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
variable (E : Type) [Field E] [NumberField E] [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
  [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
  [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
  [IsGalois ℚ E]
variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem inertiaDegIn_cases (hKn : ¬ Normal ℚ K) (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    p.asIdeal.inertiaDegIn (𝓞 E) = 1 ∨ p.asIdeal.inertiaDegIn (𝓞 E) = 2 ∨ p.asIdeal.inertiaDegIn (𝓞 E) = 3 := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain rfl := algebra_ringOfIntegers_rat_eq E ‹Algebra (𝓞 ℚ) (𝓞 E)›
  obtain ⟨φ, rfl⟩ := exists_algHom_algebra_eq K E ‹Algebra (𝓞 K) (𝓞 E)›
  letI : Algebra K E := φ.toAlgebra
  haveI : IsScalarTower ℚ K E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact inertiaDegIn_cases_canonical p K hKn hE hp

private theorem shape_of_inertiaDegIn_eq_one (hK : Module.finrank ℚ K = 3) (hL : Module.finrank ℚ L = 2)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (h1 : p.asIdeal.inertiaDegIn (𝓞 E) = 1) :
    (∃ a b c : HeightOneSpectrum (𝓞 K), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ primeFibre ℚ K p = {a, b, c} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' c.asIdeal = 1) ∧
    (∃ a b : HeightOneSpectrum (𝓞 L), a ≠ b ∧ primeFibre ℚ L p = {a, b} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 1 ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = a ∧ a.asIdeal.inertiaDeg' 𝔔.asIdeal = 1) ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = b ∧ b.asIdeal.inertiaDeg' 𝔔.asIdeal = 1)) := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain rfl := algebra_ringOfIntegers_rat_eq L ‹Algebra (𝓞 ℚ) (𝓞 L)›
  obtain rfl := algebra_ringOfIntegers_rat_eq E ‹Algebra (𝓞 ℚ) (𝓞 E)›
  obtain ⟨φ, rfl⟩ := exists_algHom_algebra_eq K E ‹Algebra (𝓞 K) (𝓞 E)›
  obtain ⟨ψ, rfl⟩ := exists_algHom_algebra_eq L E ‹Algebra (𝓞 L) (𝓞 E)›
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra L E := ψ.toAlgebra
  haveI : IsScalarTower ℚ K E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : IsScalarTower ℚ L E := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  exact shape_one_canonical p K L hK hL hp h1

private theorem shape_of_inertiaDegIn_eq_two (hKn : ¬ Normal ℚ K) (hK : Module.finrank ℚ K = 3)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (h2 : p.asIdeal.inertiaDegIn (𝓞 E) = 2) :
    (∃ a b : HeightOneSpectrum (𝓞 K), a ≠ b ∧ primeFibre ℚ K p = {a, b} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 2) ∧
    (∃ a : HeightOneSpectrum (𝓞 L), primeFibre ℚ L p = {a} ∧ p.asIdeal.inertiaDeg' a.asIdeal = 2 ∧
      ∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = a ∧ a.asIdeal.inertiaDeg' 𝔔.asIdeal = 1) := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain rfl := algebra_ringOfIntegers_rat_eq L ‹Algebra (𝓞 ℚ) (𝓞 L)›
  obtain rfl := algebra_ringOfIntegers_rat_eq E ‹Algebra (𝓞 ℚ) (𝓞 E)›
  obtain ⟨φ, rfl⟩ := exists_algHom_algebra_eq K E ‹Algebra (𝓞 K) (𝓞 E)›
  obtain ⟨ψ, rfl⟩ := exists_algHom_algebra_eq L E ‹Algebra (𝓞 L) (𝓞 E)›
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra L E := ψ.toAlgebra
  haveI : IsScalarTower ℚ K E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : IsScalarTower ℚ L E := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  exact shape_two_canonical p K L hKn hK hL hE hp h2

private theorem shape_of_inertiaDegIn_eq_three (hK : Module.finrank ℚ K = 3) (hL : Module.finrank ℚ L = 2)
    (hE : Module.finrank ℚ E = 6)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (h3 : p.asIdeal.inertiaDegIn (𝓞 E) = 3) :
    (∃ a : HeightOneSpectrum (𝓞 K), primeFibre ℚ K p = {a} ∧ p.asIdeal.inertiaDeg' a.asIdeal = 3) ∧
    (∃ a b : HeightOneSpectrum (𝓞 L), a ≠ b ∧ primeFibre ℚ L p = {a, b} ∧
      p.asIdeal.inertiaDeg' a.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' b.asIdeal = 1 ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = a ∧ a.asIdeal.inertiaDeg' 𝔔.asIdeal = 3) ∧
      (∃ 𝔔 : HeightOneSpectrum (𝓞 E), 𝔔.under (𝓞 L) = b ∧ b.asIdeal.inertiaDeg' 𝔔.asIdeal = 3)) := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain rfl := algebra_ringOfIntegers_rat_eq L ‹Algebra (𝓞 ℚ) (𝓞 L)›
  obtain rfl := algebra_ringOfIntegers_rat_eq E ‹Algebra (𝓞 ℚ) (𝓞 E)›
  obtain ⟨φ, rfl⟩ := exists_algHom_algebra_eq K E ‹Algebra (𝓞 K) (𝓞 E)›
  obtain ⟨ψ, rfl⟩ := exists_algHom_algebra_eq L E ‹Algebra (𝓞 L) (𝓞 E)›
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra L E := ψ.toAlgebra
  haveI : IsScalarTower ℚ K E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : IsScalarTower ℚ L E := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  exact shape_three_canonical p K L hK hL hE hp h3

end Types

private theorem zetaEulerPoly_eq_of_types
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (p : HeightOneSpectrum (𝓞 ℚ)) (c : HeightOneSpectrum (𝓞 L) → ℂ)
    (H1 : ∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔮.under (𝓞 ℚ) = p →
      𝔔.under (𝓞 L) = 𝔮 → IsPrimitiveRoot (c 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal))
    (H3 : ∀ 𝔮 𝔮' : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
      c 𝔮' = (c 𝔮)⁻¹)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p →
      p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    zetaEulerPoly K p = (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ c p := by
  rw [zetaEulerPoly_eq_induced_one]
  rcases inertiaDegIn_cases K E p hKn hE hp with h | h | h
  ·
    obtain ⟨⟨a, b, d, hab, had, hbd, hfibK, hfa, hfb, hfd⟩,
      ⟨q, q', hqq', hfibL, hfq, hfq', ⟨Q, hQ, hQf⟩, ⟨Q', hQ', hQ'f⟩⟩⟩ :=
      shape_of_inertiaDegIn_eq_one K L E p hK hL hp h
    have hap : a.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq K p hfibK (by simp)
    have hbp : b.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq K p hfibK (by simp)
    have hdp : d.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq K p hfibK (by simp)
    have hqp : q.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq L p hfibL (by simp)
    have hq'p : q'.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq L p hfibL (by simp)
    have hcq : c q = 1 := by
      have h1 := H1 q Q hqp hQ
      rw [hQf] at h1
      exact IsPrimitiveRoot.one_right_iff.mp h1
    have hcq' : c q' = 1 := by
      have h1 := H1 q' Q' hq'p hQ'
      rw [hQ'f] at h1
      exact IsPrimitiveRoot.one_right_iff.mp h1
    rw [inducedEulerPoly_eq_of_fibre_eq_triple K p _ hab had hbd hfibK,
      inducedEulerPoly_eq_of_fibre_eq_pair L p c hqq' hfibL,
      inducedFactor_eq_of_under K p _ hap, inducedFactor_eq_of_under K p _ hbp, inducedFactor_eq_of_under K p _ hdp,
      inducedFactor_eq_of_under L p c hqp, inducedFactor_eq_of_under L p c hq'p,
      hfa, hfb, hfd, hfq, hfq', hcq, hcq']
    simp only [Polynomial.C_1, one_mul, pow_one]
  ·
    obtain ⟨⟨a, b, hab, hfibK, hfa, hfb⟩, ⟨q, hfibL, hfq, ⟨Q, hQ, hQf⟩⟩⟩ :=
      shape_of_inertiaDegIn_eq_two K L E p hKn hK hL hE hp h
    have hap : a.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq K p hfibK (by simp)
    have hbp : b.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq K p hfibK (by simp)
    have hqp : q.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq L p hfibL (by simp)
    have hcq : c q = 1 := by
      have h1 := H1 q Q hqp hQ
      rw [hQf] at h1
      exact IsPrimitiveRoot.one_right_iff.mp h1
    rw [inducedEulerPoly_eq_of_fibre_eq_pair K p _ hab hfibK,
      inducedEulerPoly_eq_of_fibre_eq_singleton L p c hfibL,
      inducedFactor_eq_of_under K p _ hap, inducedFactor_eq_of_under K p _ hbp,
      inducedFactor_eq_of_under L p c hqp, hfa, hfb, hfq, hcq]
    simp only [Polynomial.C_1, one_mul, pow_one]
  ·
    obtain ⟨⟨a, hfibK, hfa⟩, ⟨q, q', hqq', hfibL, hfq, hfq', ⟨Q, hQ, hQf⟩, ⟨Q', hQ', hQ'f⟩⟩⟩ :=
      shape_of_inertiaDegIn_eq_three K L E p hK hL hE hp h
    have hap : a.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq K p hfibK (by simp)
    have hqp : q.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq L p hfibL (by simp)
    have hq'p : q'.under (𝓞 ℚ) = p := mem_fibre_of_fibre_eq L p hfibL (by simp)
    have hζ : IsPrimitiveRoot (c q) 3 := by
      have h1 := H1 q Q hqp hQ
      rwa [hQf] at h1
    have hcq' : c q' = (c q)⁻¹ := H3 q q' hqp hq'p hqq'
    rw [inducedEulerPoly_eq_of_fibre_eq_singleton K p _ hfibK,
      inducedEulerPoly_eq_of_fibre_eq_pair L p c hqq' hfibL,
      inducedFactor_eq_of_under K p _ hap, inducedFactor_eq_of_under L p c hqp, inducedFactor_eq_of_under L p c hq'p,
      hfa, hfq, hfq', hcq']
    simp only [Polynomial.C_1, one_mul, pow_one]
    exact (cube_identity hζ).symm

end ZetaEulerOfResolvent

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (p : HeightOneSpectrum (𝓞 ℚ)) (c : HeightOneSpectrum (𝓞 L) → ℂ)
    (H1 : ∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔮.under (𝓞 ℚ) = p →
      𝔔.under (𝓞 L) = 𝔮 → IsPrimitiveRoot (c 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal))
    (H3 : ∀ 𝔮 𝔮' : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
      c 𝔮' = (c 𝔮)⁻¹)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p →
      p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    zetaEulerPoly K p = (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ c p :=
  ZetaEulerOfResolvent.zetaEulerPoly_eq_of_types K L E hK hKn hL hE p c H1 H3 hp

end S_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent
end P2MW
export P2MW.S_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent (solution)
