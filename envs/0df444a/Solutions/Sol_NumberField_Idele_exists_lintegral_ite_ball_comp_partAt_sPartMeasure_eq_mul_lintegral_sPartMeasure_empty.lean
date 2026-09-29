-- Prove2me | solution 1 for NumberField.Idele.exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/baa181da-5ca1-5a2e-a26e-b4586ef3f0ec

import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_NumberField_AdelicLevel
import Mathlib
import Theorems.Thm_NumberField_Idele_measurePreserving_mul_right_sPartMeasure
import Theorems.Thm_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace RS40P2

open NumberField.Idele NumberField.AdelicLevel AutomorphicForm Topology Filter Set

variable (K : Type) [Field K] [NumberField K]

section LCoverFinite

theorem exists_finset_sphere_mulCover (v : HeightOneSpectrum (𝓞 K)) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    ∃ Z : Finset (v.adicCompletion K), (∀ z ∈ Z, Valued.v z = WithZero.exp a) ∧
      ∀ u : v.adicCompletion K, Valued.v u = WithZero.exp a →
        ∃ z ∈ Z, Valued.v (z⁻¹ * u - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  by_cases hne : ∃ u₀ : v.adicCompletion K, Valued.v u₀ = WithZero.exp a
  swap
  · refine ⟨∅, by simp, fun u hu => (hne ⟨u, hu⟩).elim⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀0 : u₀ ≠ 0 := fun h => by rw [h, map_zero] at hu₀; exact WithZero.exp_ne_zero hu₀.symm

  obtain ⟨tn, htn0, htn⟩ := exists_valued_eq_exp_neg (K := K) v n

  haveI : CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr inferInstance

  let B : v.adicCompletion K → Set (v.adicCompletion K) := fun z => {u | Valued.v (u - z) ≤ Valued.v tn}
  have hBopen : ∀ z, IsOpen (B z) := fun z =>
    (isOpen_setOf_valued_le v tn htn0).preimage (continuous_id.sub continuous_const)
  have hcover : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ⊆ ⋃ z, B z := fun u _ =>
    Set.mem_iUnion.mpr ⟨u, by show Valued.v (u - u) ≤ _; rw [sub_self, map_zero]; exact zero_le'⟩
  obtain ⟨T, hT⟩ := hO.elim_finite_subcover B hBopen hcover
  refine ⟨(T.filter fun z => Valued.v z = 1).image (fun z => u₀ * z), ?_, ?_⟩
  · intro z hz
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hz
    rw [map_mul, hu₀, (Finset.mem_filter.mp hz₁).2, mul_one]
  · intro u hu

    have hu' : Valued.v (u₀⁻¹ * u) = 1 := by
      rw [map_mul, map_inv₀, hu₀, hu, inv_mul_cancel₀ WithZero.exp_ne_zero]
    have hu'O : u₀⁻¹ * u ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, hu']
    obtain ⟨z, hzT, hz⟩ : ∃ z ∈ T, u₀⁻¹ * u ∈ B z := by
      simpa only [Set.mem_iUnion, exists_prop] using hT hu'O
    have hzclose : Valued.v (u₀⁻¹ * u - z) ≤ WithZero.exp (-(n : ℤ)) := by rw [← htn]; exact hz

    have hlt : Valued.v (z - u₀⁻¹ * u) < Valued.v (u₀⁻¹ * u) := by
      rw [Valuation.map_sub_swap, hu']
      refine lt_of_le_of_lt hzclose ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hz1 : Valued.v z = 1 := by
      rw [← hu']
      exact Valuation.map_eq_of_sub_lt Valued.v hlt
    have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
    refine ⟨u₀ * z, Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzT, hz1⟩, rfl⟩, ?_⟩
    have e : (u₀ * z)⁻¹ * u - 1 = z⁻¹ * (u₀⁻¹ * u - z) := by field_simp
    rw [e, map_mul, map_inv₀, hz1, inv_one, one_mul]
    exact hzclose

end LCoverFinite

section Shell
variable {K}

def unitOf {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) : (v.adicCompletion K)ˣ :=
  if h : x = 0 then 1 else Units.mk0 x h

theorem unitOf_coe {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (hx : x ≠ 0) :
    (unitOf x : v.adicCompletion K) = x := by
  simp [unitOf, hx]

variable (K)

def shellIdele (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    (AdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ S, Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (unitOf (z v)))

theorem finAdele_prod_apply {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) : (∏ i ∈ s, f i) w = ∏ i ∈ s, f i w :=
  map_prod (finAdeleEval (𝓞 K) K w) f s

theorem shellIdele_fst (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    ((shellIdele K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  rw [shellIdele, Units.coe_prod]
  change adeleArch (𝓞 K) K (∏ i ∈ S, ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K i (unitOf (z i))) :
    (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = 1
  rw [map_prod]
  exact Finset.prod_eq_one fun v _ => rfl

theorem shellIdele_snd_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (w : HeightOneSpectrum (𝓞 K)) :
    ((shellIdele K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w =
      if w ∈ S then ((unitOf (z w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
  rw [shellIdele, Units.coe_prod]
  change ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K))
    (∏ i ∈ S, ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K i (unitOf (z i))) :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = _
  rw [map_prod]
  have h : ∀ v ∈ S, ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K))
      (((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (unitOf (z v))) :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        if v = w then ((unitOf (z w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
    intro v _
    show ((localUnit (𝓞 K) K v (unitOf (z v)) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = _
    by_cases hvw : v = w
    · subst hvw
      rw [if_pos rfl]
      exact localUnit_apply_self _ _ _ _
    · rw [if_neg hvw]
      exact localUnit_apply_of_ne _ _ _ _ (Ne.symm hvw)
  rw [Finset.prod_congr rfl h, Finset.prod_ite_eq']

theorem units_inv_snd_apply (s : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w = (((s : AdeleRing (𝓞 K) K)).2 w)⁻¹ := by
  have h : ((s : AdeleRing (𝓞 K) K)).2 w * (((s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w = 1 := by
    have : (((s * s⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w = 1 := by rw [mul_inv_cancel]; rfl
    exact this
  have hs0 : ((s : AdeleRing (𝓞 K) K)).2 w ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact (eq_inv_of_mul_eq_one_right h)

end Shell

theorem idele_ext {a b : (AdeleRing (𝓞 K) K)ˣ} (h1 : ((a : AdeleRing (𝓞 K) K)).1 = ((b : AdeleRing (𝓞 K) K)).1)
    (h2 : ∀ v, ((a : AdeleRing (𝓞 K) K)).2 v = ((b : AdeleRing (𝓞 K) K)).2 v) : a = b := by
  apply Units.ext
  exact Prod.ext h1 (RestrictedProduct.ext _ _ fun v => h2 v)

theorem partAt_empty_eq_one_of_fst {u : (AdeleRing (𝓞 K) K)ˣ} (hu : ((u : AdeleRing (𝓞 K) K)).1 = 1) :
    partAt K ∅ u = 1 := by
  apply idele_ext K
  · rw [partAt_fst, hu]; rfl
  · intro v; rw [partAt_snd_of_not_mem K ∅ u (Finset.notMem_empty v)]; rfl

theorem partAt_empty_partAt_empty (a : (AdeleRing (𝓞 K) K)ˣ) : partAt K ∅ (partAt K ∅ a) = partAt K ∅ a := by
  apply idele_ext K
  · rw [partAt_fst, partAt_fst]
  · intro v
    rw [partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v), partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v)]

theorem partAt_empty_eq_of_fst_eq {a b : (AdeleRing (𝓞 K) K)ˣ}
    (h : ((a : AdeleRing (𝓞 K) K)).1 = ((b : AdeleRing (𝓞 K) K)).1) : partAt K ∅ a = partAt K ∅ b := by
  apply idele_ext K
  · rw [partAt_fst, partAt_fst, h]
  · intro v
    rw [partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v), partAt_snd_of_not_mem K ∅ _ (Finset.notMem_empty v)]

theorem continuous_snd_apply (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((t : AdeleRing (𝓞 K) K)).2 v :=
  ((RestrictedProduct.continuous_eval v).comp continuous_snd).comp Units.continuous_val

section Local

variable {K}
variable {v : HeightOneSpectrum (𝓞 K)}

def lball (ρ : WithZero (Multiplicative ℤ)) (z : v.adicCompletion K) : Set (v.adicCompletion K) :=
  {u | Valued.v (u - z) ≤ ρ}

theorem mem_lball {ρ : WithZero (Multiplicative ℤ)} {z u : v.adicCompletion K} : u ∈ lball ρ z ↔ Valued.v (u - z) ≤ ρ :=
  Iff.rfl

theorem lball_eq_of_mem {ρ : WithZero (Multiplicative ℤ)} {z u : v.adicCompletion K} (hu : u ∈ lball ρ z) :
    lball ρ u = lball ρ z := by
  ext w
  simp only [mem_lball] at hu ⊢
  constructor
  · intro hw
    have : w - z = (w - u) + (u - z) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hw hu)
  · intro hw
    have : w - u = (w - z) - (u - z) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hw hu)

theorem lball_eq_of_mem_of_mem {ρ : WithZero (Multiplicative ℤ)} {z z' u : v.adicCompletion K}
    (hu : u ∈ lball ρ z) (hu' : u ∈ lball ρ z') : lball ρ z = lball ρ z' := by
  rw [← lball_eq_of_mem hu, lball_eq_of_mem hu']

theorem valued_eq_of_mem_lball {ρ : WithZero (Multiplicative ℤ)} {z u : v.adicCompletion K}
    (hρ : ρ < Valued.v z) (hu : u ∈ lball ρ z) : Valued.v u = Valued.v z := by
  have hlt : Valued.v (u - z) < Valued.v z := lt_of_le_of_lt hu hρ
  exact Valuation.map_eq_of_sub_lt Valued.v hlt

theorem isOpen_lball {ρ : WithZero (Multiplicative ℤ)} (tn : v.adicCompletion K) (htn0 : tn ≠ 0) (hρ : Valued.v tn = ρ)
    (z : v.adicCompletion K) : IsOpen (lball ρ z) := by
  rw [← hρ]
  exact (isOpen_setOf_valued_le v tn htn0).preimage (continuous_id.sub continuous_const)

end Local

end RS40P2

namespace RS40P2

open NumberField.Idele NumberField.AdelicLevel AutomorphicForm Topology Filter Set MeasureTheory

variable (K : Type) [Field K] [NumberField K]

theorem snd_mul (a b : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((a * b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = ((a : AdeleRing (𝓞 K) K)).2 v * ((b : AdeleRing (𝓞 K) K)).2 v :=
  rfl

theorem snd_ne_zero (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ((a : AdeleRing (𝓞 K) K)).2 v ≠ 0 := by
  intro h
  have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [mul_inv_cancel]; rfl
  rw [snd_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem valued_eq_iff_ord_eq (v : HeightOneSpectrum (𝓞 K)) (t t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ↔ ord K v t = ord K v t₀ := by
  rw [valued_snd_eq_exp_neg_ord, valued_snd_eq_exp_neg_ord, WithZero.exp_injective.eq_iff, neg_inj]

theorem main
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (nb : ℕ) (hnb : 0 < nb) :
    ∃ N : ℕ, 0 < N ∧
      MeasurableSet {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
          Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} ∧
      ∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
        (N : ℝ≥0∞) * ∫⁻ t, {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
          Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}.indicator
            (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) =
        ∫⁻ t, f t ∂(sPartMeasure K ∅) := by

  set e : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) with he
  have he' : e = WithZero.exp (-(nb : ℤ)) := rfl
  have he1 : e < 1 := by
    rw [he', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  set c : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v => ((t₀ : AdeleRing (𝓞 K) K)).2 v with hc
  have hc0 : ∀ v, c v ≠ 0 := fun v => snd_ne_zero K t₀ v
  have hcv0 : ∀ v, Valued.v (c v) ≠ 0 := fun v h => hc0 v ((Valuation.zero_iff _).1 h)
  set ρ : ∀ v : HeightOneSpectrum (𝓞 K), WithZero (Multiplicative ℤ) := fun v => Valued.v (c v) * e with hρ
  have hρlt : ∀ v, ρ v < Valued.v (c v) := fun v => by
    have hcexp : Valued.v (c v) = WithZero.exp (-ord K v t₀) := valued_snd_eq_exp_neg_ord K v t₀
    show Valued.v (c v) * e < Valued.v (c v)
    rw [hcexp, he', ← WithZero.exp_add, WithZero.exp_lt_exp]
    omega

  have hrad : ∀ v : HeightOneSpectrum (𝓞 K), ∃ tn : v.adicCompletion K, tn ≠ 0 ∧ Valued.v tn = ρ v := by
    intro v
    obtain ⟨tn, htn0, htn⟩ := exists_valued_eq_exp_neg (K := K) v nb
    refine ⟨c v * tn, mul_ne_zero (hc0 v) htn0, ?_⟩
    rw [map_mul, htn, hρ, he']

  set Ball : Set (AdeleRing (𝓞 K) K)ˣ := {t | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
      Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * e} with hBall
  set Shell : Set (AdeleRing (𝓞 K) K)ˣ := {t | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (c v)} with hShell
  have hBallmem : ∀ t, t ∈ Ball ↔ ∀ v ∈ S, ((t : AdeleRing (𝓞 K) K)).2 v ∈ lball (ρ v) (c v) := fun t => Iff.rfl

  have hmeas_local : ∀ (A : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)), (∀ v ∈ S, IsOpen (A v)) →
      MeasurableSet {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, ((t : AdeleRing (𝓞 K) K)).2 v ∈ A v} := by
    intro A hA
    have : {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, ((t : AdeleRing (𝓞 K) K)).2 v ∈ A v} =
        ⋂ v ∈ S, (fun t : (AdeleRing (𝓞 K) K)ˣ => ((t : AdeleRing (𝓞 K) K)).2 v) ⁻¹' A v := by
      ext t; simp only [mem_setOf_eq, mem_iInter, mem_preimage]
    rw [this]
    exact (isOpen_biInter_finset fun v hv => (hA v hv).preimage (continuous_snd_apply K v)).measurableSet
  have hBallMeas : MeasurableSet Ball := by
    refine hmeas_local (fun v => lball (ρ v) (c v)) fun v _ => ?_
    obtain ⟨tn, htn0, htn⟩ := hrad v
    exact isOpen_lball tn htn0 htn _

  have hcover : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Z : Finset (v.adicCompletion K), (∀ z ∈ Z, Valued.v z = Valued.v (c v)) ∧
      ∀ u : v.adicCompletion K, Valued.v u = Valued.v (c v) → ∃ z ∈ Z, u ∈ lball (ρ v) z := by
    intro v
    have hcexp : Valued.v (c v) = WithZero.exp (-ord K v t₀) := valued_snd_eq_exp_neg_ord K v t₀
    obtain ⟨Z, hZ1, hZ2⟩ := exists_finset_sphere_mulCover K v (-ord K v t₀) nb hnb
    refine ⟨Z, fun z hz => (hZ1 z hz).trans hcexp.symm, fun u hu => ?_⟩
    obtain ⟨z, hz, hzu⟩ := hZ2 u (hu.trans hcexp)
    refine ⟨z, hz, ?_⟩
    have hz0 : z ≠ 0 := fun h => by
      have := hZ1 z hz; rw [h, map_zero] at this; exact WithZero.exp_ne_zero this.symm
    show Valued.v (u - z) ≤ ρ v
    have : u - z = z * (z⁻¹ * u - 1) := by field_simp
    rw [this, map_mul, hρ, (hZ1 z hz).trans hcexp.symm]
    exact mul_le_mul_right hzu _
  choose Z hZval hZcov using hcover
  set R : ∀ v : HeightOneSpectrum (𝓞 K), Finset (Set (v.adicCompletion K)) := fun v => (Z v).image (lball (ρ v)) with hR
  have hR1 : ∀ v, ∀ A ∈ R v, ∃ z, Valued.v z = Valued.v (c v) ∧ A = lball (ρ v) z := by
    intro v A hA
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hA
    exact ⟨z, hZval v z hz, rfl⟩
  have hR2 : ∀ v, ∀ A ∈ R v, ∀ A' ∈ R v, ∀ u, u ∈ A → u ∈ A' → A = A' := by
    intro v A hA A' hA' u hu hu'
    obtain ⟨z, -, rfl⟩ := hR1 v A hA
    obtain ⟨z', -, rfl⟩ := hR1 v A' hA'
    exact lball_eq_of_mem_of_mem hu hu'
  have hR3 : ∀ v, ∀ u : v.adicCompletion K, Valued.v u = Valued.v (c v) → ∃ A ∈ R v, u ∈ A := by
    intro v u hu
    obtain ⟨z, hz, hzu⟩ := hZcov v u hu
    exact ⟨lball (ρ v) z, Finset.mem_image.2 ⟨z, hz, rfl⟩, hzu⟩
  have hR4 : ∀ v, ∀ A ∈ R v, ∀ u ∈ A, Valued.v u = Valued.v (c v) := by
    intro v A hA u hu
    obtain ⟨z, hz, rfl⟩ := hR1 v A hA
    rw [← hz]
    exact valued_eq_of_mem_lball (hz ▸ hρlt v) hu
  have hRopen : ∀ v, ∀ A ∈ R v, IsOpen A := by
    intro v A hA
    obtain ⟨z, -, rfl⟩ := hR1 v A hA
    obtain ⟨tn, htn0, htn⟩ := hrad v
    exact isOpen_lball tn htn0 htn _

  set Pi : Finset (∀ v ∈ S, Set (v.adicCompletion K)) := S.pi R with hPi
  set MB : (∀ v ∈ S, Set (v.adicCompletion K)) → Set (AdeleRing (𝓞 K) K)ˣ :=
    fun b => {t | ∀ v (hv : v ∈ S), ((t : AdeleRing (𝓞 K) K)).2 v ∈ b v hv} with hMB
  have hMBmeas : ∀ b ∈ Pi, MeasurableSet (MB b) := by
    intro b hb
    have : MB b = {t : (AdeleRing (𝓞 K) K)ˣ | ∀ v ∈ S, ((t : AdeleRing (𝓞 K) K)).2 v ∈ (if hv : v ∈ S then b v hv else univ)} := by
      ext t; simp only [hMB, mem_setOf_eq]
      constructor
      · intro h v hv; rw [dif_pos hv]; exact h v hv
      · intro h v hv; have := h v hv; rwa [dif_pos hv] at this
    rw [this]
    refine hmeas_local _ fun v hv => ?_
    rw [dif_pos hv]
    exact hRopen v _ (Finset.mem_pi.1 hb v hv)

  have hpart : ∀ (G : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (t : (AdeleRing (𝓞 K) K)ˣ),
      ∑ b ∈ Pi, (MB b).indicator G t = Shell.indicator G t := by
    intro G t
    by_cases hsh : t ∈ Shell
    ·
      have hex : ∀ v (hv : v ∈ S), ∃ A ∈ R v, ((t : AdeleRing (𝓞 K) K)).2 v ∈ A := fun v hv => hR3 v _ (hsh v hv)
      set b₀ : ∀ v ∈ S, Set (v.adicCompletion K) := fun v hv => Classical.choose (hex v hv) with hb₀
      have hb₀spec : ∀ v (hv : v ∈ S), b₀ v hv ∈ R v ∧ ((t : AdeleRing (𝓞 K) K)).2 v ∈ b₀ v hv :=
        fun v hv => Classical.choose_spec (hex v hv)
      have hb0Pi : b₀ ∈ Pi := Finset.mem_pi.2 fun v hv => (hb₀spec v hv).1
      have ht₀ : t ∈ MB b₀ := fun v hv => (hb₀spec v hv).2
      have huniq : ∀ b ∈ Pi, t ∈ MB b → b = b₀ := by
        intro b hb htb
        funext v hv
        exact hR2 v _ (Finset.mem_pi.1 hb v hv) _ (hb₀spec v hv).1 _ (htb v hv) (hb₀spec v hv).2
      rw [Finset.sum_eq_single_of_mem b₀ hb0Pi (fun b hb hne => indicator_of_notMem (fun htb => hne (huniq b hb htb)) _),
        indicator_of_mem ht₀, indicator_of_mem hsh]
    · rw [indicator_of_notMem hsh]
      refine Finset.sum_eq_zero fun b hb => indicator_of_notMem (fun htb => hsh ?_) _
      intro v hv
      exact hR4 v _ (Finset.mem_pi.1 hb v hv) _ (htb v hv)

  have hcentre : ∀ b ∈ Pi, ∃ z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K,
      ∀ v (hv : v ∈ S), Valued.v (z v) = Valued.v (c v) ∧ b v hv = lball (ρ v) (z v) := by
    intro b hb
    have : ∀ v, ∃ zv : v.adicCompletion K, ∀ hv : v ∈ S, Valued.v zv = Valued.v (c v) ∧ b v hv = lball (ρ v) zv := by
      intro v
      by_cases hv : v ∈ S
      · obtain ⟨z, hz, hbz⟩ := hR1 v _ (Finset.mem_pi.1 hb v hv)
        exact ⟨z, fun _ => ⟨hz, hbz⟩⟩
      · exact ⟨0, fun h => (hv h).elim⟩
    choose z hz using this
    exact ⟨z, fun v hv => hz v hv⟩

  have hMBint : ∀ b ∈ Pi, ∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
      ∫⁻ t, (MB b).indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) =
        ∫⁻ t, Ball.indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) := by
    intro b hb f hf
    obtain ⟨z, hz⟩ := hcentre b hb

    set lam : (AdeleRing (𝓞 K) K)ˣ := shellIdele K S (fun v => z v / c v) with hlam
    have hzc0 : ∀ v ∈ S, z v / c v ≠ 0 := fun v hv => by
      refine div_ne_zero (fun h => ?_) (hc0 v)
      have := (hz v hv).1; rw [h, map_zero] at this; exact hcv0 v this.symm
    have hlam1 : ((lam : AdeleRing (𝓞 K) K)).1 = 1 := shellIdele_fst K S _
    have hlamS : ∀ v ∈ S, ((lam : AdeleRing (𝓞 K) K)).2 v = z v / c v := fun v hv => by
      rw [hlam, shellIdele_snd_apply, if_pos hv, unitOf_coe _ (hzc0 v hv)]
    have hlamoff : ∀ v, v ∉ S → ((lam : AdeleRing (𝓞 K) K)).2 v = 1 := fun v hv => by
      rw [hlam, shellIdele_snd_apply, if_neg hv]
    have hlaminv_off : ∀ v, v ∉ S → (((lam⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := fun v hv => by
      rw [units_inv_snd_apply, hlamoff v hv, inv_one]

    have hkey : ∀ t, t ∈ MB b ↔ t * lam⁻¹ ∈ Ball := by
      intro t
      simp only [hMB, hBall, mem_setOf_eq]
      refine forall₂_congr fun v hv => ?_
      rw [(hz v hv).2, mem_lball, snd_mul, units_inv_snd_apply, hlamS v hv]
      have hcz : ((t : AdeleRing (𝓞 K) K)).2 v * (z v / c v)⁻¹ - c v = (c v / z v) * (((t : AdeleRing (𝓞 K) K)).2 v - z v) := by
        have hz0 : z v ≠ 0 := fun h => by have := (hz v hv).1; rw [h, map_zero] at this; exact hcv0 v this.symm
        field_simp [hc0 v, hz0]
        try ring
      rw [hcz, map_mul, map_div₀, (hz v hv).1, div_self (hcv0 v), one_mul]

    have hind : (MB b).indicator (fun t => f (partAt K ∅ t)) =
        fun t => Ball.indicator (fun s => f (partAt K ∅ s)) (t * lam⁻¹) := by
      funext t
      by_cases ht : t ∈ MB b
      · rw [indicator_of_mem ht, indicator_of_mem ((hkey t).1 ht)]
        congr 1
        rw [map_mul, map_inv, partAt_empty_eq_one_of_fst K hlam1, inv_one, mul_one]
      · rw [indicator_of_notMem ht, indicator_of_notMem (fun h => ht ((hkey t).2 h))]
    rw [hind]
    have hmp := NumberField.Idele.measurePreserving_mul_right_sPartMeasure K S lam⁻¹ hlaminv_off
    exact hmp.lintegral_comp ((hf.comp (measurable_partAt K ∅)).indicator hBallMeas)

  have hshellint : ∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
      ∫⁻ t, Shell.indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) = ∫⁻ t, f t ∂(sPartMeasure K ∅) := by
    intro f hf
    set φ : HeightOneSpectrum (𝓞 K) → ℤ → ℝ≥0∞ := fun v m => if m = ord K v t₀ then 1 else 0 with hφ
    have hG1 : ∀ a b : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).1 = ((b : AdeleRing (𝓞 K) K)).1 →
        f (partAt K ∅ a) = f (partAt K ∅ b) := fun a b h => by rw [partAt_empty_eq_of_fst_eq K h]
    have hCH := NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum K S
      (fun t => f (partAt K ∅ t)) (hf.comp (measurable_partAt K ∅)) hG1 φ
    have hprod : ∀ t : (AdeleRing (𝓞 K) K)ˣ, (f (partAt K ∅ t) * ∏ v ∈ S, φ v (ord K v t)) =
        Shell.indicator (fun t => f (partAt K ∅ t)) t := by
      intro t
      by_cases ht : t ∈ Shell
      · rw [indicator_of_mem ht, Finset.prod_eq_one (fun v hv => ?_), mul_one]
        rw [hφ]; show (if ord K v t = ord K v t₀ then (1 : ℝ≥0∞) else 0) = 1
        rw [if_pos ((valued_eq_iff_ord_eq K v t t₀).1 (ht v hv))]
      · rw [indicator_of_notMem ht]
        have : ∃ v ∈ S, ¬ Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (c v) := by
          by_contra h; push Not at h; exact ht h
        obtain ⟨v, hv, hne⟩ := this
        rw [Finset.prod_eq_zero hv, mul_zero]
        show (if ord K v t = ord K v t₀ then (1 : ℝ≥0∞) else 0) = 0
        rw [if_neg (fun h => hne ((valued_eq_iff_ord_eq K v t t₀).2 h))]
    have htsum : ∀ v ∈ S, ∑' m : ℤ, φ v m = 1 := fun v _ => by
      rw [hφ]; simpa using tsum_ite_eq (ord K v t₀) (fun _ : ℤ => (1 : ℝ≥0∞))
    simp_rw [hprod] at hCH
    rw [hCH, Finset.prod_eq_one htsum, mul_one]

    have hFm : Measurable (fun t : (AdeleRing (𝓞 K) K)ˣ => f (partAt K ∅ t)) := hf.comp (measurable_partAt K ∅)
    rw [sPartMeasure, lintegral_map hFm (measurable_partAt K ∅), lintegral_map hf (measurable_partAt K ∅)]
    simp_rw [partAt_empty_partAt_empty]

  have hPine : Pi.Nonempty := by
    rw [hPi, Finset.pi_nonempty]
    intro v _
    obtain ⟨A, hA, -⟩ := hR3 v (c v) rfl
    exact ⟨A, hA⟩
  refine ⟨Pi.card, Finset.card_pos.2 hPine, hBallMeas, fun f hf => ?_⟩
  calc (Pi.card : ℝ≥0∞) * ∫⁻ t, Ball.indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S)
      = ∑ b ∈ Pi, ∫⁻ t, (MB b).indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) := by
        rw [Finset.sum_congr rfl fun b hb => hMBint b hb f hf, Finset.sum_const, nsmul_eq_mul]
    _ = ∫⁻ t, ∑ b ∈ Pi, (MB b).indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) := by
        rw [lintegral_finset_sum]
        intro b hb
        exact ((hf.comp (measurable_partAt K ∅)).indicator (hMBmeas b hb))
    _ = ∫⁻ t, Shell.indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) := by
        simp_rw [hpart]
    _ = ∫⁻ t, f t ∂(sPartMeasure K ∅) := hshellint f hf

end RS40P2

open RS40P2 NumberField.Idele MeasureTheory Set in
theorem solution
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
    (nb : ℕ) (_hnb : 0 < nb) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
        (∫⁻ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            ∂(NumberField.Idele.sPartMeasure K S)) =
          ENNReal.ofReal κ * ∫⁻ t, f t ∂(NumberField.Idele.sPartMeasure K ∅)) ∧
      (∀ f : (AdeleRing (𝓞 K) K)ˣ → ℂ, Integrable f (NumberField.Idele.sPartMeasure K ∅) →
        Integrable (fun t : (AdeleRing (𝓞 K) K)ˣ => if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            (NumberField.Idele.sPartMeasure K S) ∧
        (∫ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            ∂(NumberField.Idele.sPartMeasure K S)) =
          (κ : ℂ) * ∫ t, f t ∂(NumberField.Idele.sPartMeasure K ∅)) := by
  obtain ⟨N, hN, hBallMeas, hmain⟩ := RS40P2.main K S t₀ nb _hnb
  set Ball : Set (AdeleRing (𝓞 K) K)ˣ := {t | ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
      Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} with hBall
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  set κ : ℝ := (N : ℝ)⁻¹ with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκenn : ENNReal.ofReal κ = (N : ℝ≥0∞)⁻¹ := by
    rw [hκ, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

  have hlin : ∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
      ∫⁻ t, Ball.indicator (fun t => f (partAt K ∅ t)) t ∂(sPartMeasure K S) = ENNReal.ofReal κ * ∫⁻ t, f t ∂(sPartMeasure K ∅) := by
    intro f hf
    rw [hκenn, ← hmain f hf, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop, one_mul]

  have hμ : (Measure.restrict (sPartMeasure K S) Ball).map (partAt K ∅) = ENNReal.ofReal κ • sPartMeasure K ∅ := by
    ext A hA
    rw [Measure.map_apply (measurable_partAt K ∅) hA, Measure.restrict_apply (hA.preimage (measurable_partAt K ∅)),
      Measure.smul_apply, smul_eq_mul]
    have h1 := hlin (A.indicator 1) (measurable_one.indicator hA)
    rw [lintegral_indicator_one hA] at h1
    rw [← h1]
    have : Ball.indicator (fun t => A.indicator (1 : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (partAt K ∅ t)) =
        ((partAt K ∅) ⁻¹' A ∩ Ball).indicator 1 := by
      funext t
      by_cases h1 : t ∈ Ball <;> by_cases h2 : partAt K ∅ t ∈ A <;>
        simp [indicator_of_mem, indicator_of_notMem, h1, h2, mem_inter_iff, mem_preimage]
    rw [this, lintegral_indicator_one ((hA.preimage (measurable_partAt K ∅)).inter hBallMeas)]
  refine ⟨κ, hκpos, ?_, ?_⟩
  · intro f hf
    have := hlin f hf
    simpa only [indicator, hBall, mem_setOf_eq] using this
  · intro f hf
    have hfm : AEStronglyMeasurable f ((Measure.restrict (sPartMeasure K S) Ball).map (partAt K ∅)) := by
      rw [hμ]; exact hf.aestronglyMeasurable.smul_measure _
    have hfi : Integrable f ((Measure.restrict (sPartMeasure K S) Ball).map (partAt K ∅)) := by
      rw [hμ]; exact hf.smul_measure ENNReal.ofReal_ne_top
    have hcomp : Integrable (fun t => f (partAt K ∅ t)) (Measure.restrict (sPartMeasure K S) Ball) :=
      (integrable_map_measure hfm (measurable_partAt K ∅).aemeasurable).1 hfi
    have hind : (fun t : (AdeleRing (𝓞 K) K)ˣ => if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0) =
        Ball.indicator (fun t => f (partAt K ∅ t)) := by
      funext t
      simp only [indicator, hBall, mem_setOf_eq]
    rw [hind]
    refine ⟨(integrable_indicator_iff hBallMeas).2 hcomp, ?_⟩
    rw [integral_indicator hBallMeas, ← integral_map (measurable_partAt K ∅).aemeasurable hfm, hμ,
      integral_smul_measure, ENNReal.toReal_ofReal hκpos.le, Complex.real_smul]

end
end S_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
end P2MW
export P2MW.S_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty (solution)
