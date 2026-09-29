-- Prove2me | solution 1 for NumberField.LevelArith.exists_placesAbove_inr_embedding_heightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bace8a4d-94bd-599b-89c5-6ecdee232c39

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

local instance PlacesF.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance PlacesF.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance PlacesF.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

scoped instance PlacesF.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"
set_option linter.unusedSectionVars false

namespace PlacesF

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma mem_nonunits_smul_iff (A : ValuationSubring Qbar) (x : Γ) (y : Qbar) :
    x • y ∈ (x • A).nonunits ↔ y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← smul_inv'',
    ValuationSubring.smul_mem_pointwise_smul_iff, smul_eq_zero_iff_eq]

lemma liesOverPrime_smul_iff (A : ValuationSubring Qbar) (x : Γ) (q : ℕ) :
    (x • A).LiesOverPrime q ↔ A.LiesOverPrime q := by
  unfold ValuationSubring.LiesOverPrime
  have : ((q : Qbar)) = x • (q : Qbar) := by
    show (q : Qbar) = x (q : Qbar)
    rw [map_natCast]
  conv_lhs => rw [this]
  exact mem_nonunits_smul_iff A x q

lemma inv_natCast_not_mem {A : ValuationSubring Qbar} {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    ((q : Qbar))⁻¹ ∉ A := by
  have h := (ValuationSubring.mem_nonunits_iff_or A).1 hA
  rcases h with h | h
  · exact absurd h (Nat.cast_ne_zero.2 hq.ne_zero)
  · exact h

lemma exists_mem_mul_eq_of_mem_closure (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ ↥L] (H : Subgroup Γ) (x d : Γ)
    (hd : d ∈ (H.topologicalClosure : Set Γ)) :
    ∃ s ∈ L.fixingSubgroup, ∃ r ∈ H, x * d = s * x * r := by
  rw [Subgroup.topologicalClosure_coe, mem_closure_iff] at hd
  let f : Γ → Γ := fun g => x * g * (d⁻¹ * x⁻¹)
  have hf : Continuous f := (continuous_const.mul continuous_id).mul continuous_const
  have hW : IsOpen (f ⁻¹' (L.fixingSubgroup : Set Γ)) := (IntermediateField.fixingSubgroup_isOpen L).preimage hf
  have hdW : d ∈ f ⁻¹' (L.fixingSubgroup : Set Γ) := by
    show x * d * (d⁻¹ * x⁻¹) ∈ L.fixingSubgroup
    rw [show x * d * (d⁻¹ * x⁻¹) = 1 by group]
    exact Subgroup.one_mem _
  obtain ⟨r, hrW, hrH⟩ := hd _ hW hdW
  refine ⟨(x * r * (d⁻¹ * x⁻¹))⁻¹, L.fixingSubgroup.inv_mem hrW, r, hrH, ?_⟩
  group

end PlacesF
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"

namespace PlacesF

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (q : ↥S)

noncomputable abbrev A : ValuationSubring Qbar := primeLocalPlace (q : Nat.Primes)

lemma qprime : (((q : Nat.Primes) : ℕ)).Prime := (q : Nat.Primes).2

lemma A_lies : (A S q).LiesOverPrime ((q : Nat.Primes) : ℕ) := ExtCitation.liesOverPrime_primeLocalPlace q

lemma range_le_decomp : (extArithLoc S (Sum.inr q)).range ≤ (A S q).decompositionSubgroup ℚ := by
  rintro _ ⟨τ, rfl⟩
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨qprime S q⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup ((q : Nat.Primes) : ℕ) τ

lemma decomp_le_closure : (A S q).decompositionSubgroup ℚ ≤ ((extArithLoc S (Sum.inr q)).range).topologicalClosure := by
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨qprime S q⟩
  exact ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal ((q : Nat.Primes) : ℕ)

lemma smul_A_eq_of_mem_range {d : Γ} (hd : d ∈ (extArithLoc S (Sum.inr q)).range) : d • A S q = A S q :=
  MulAction.mem_stabilizer_iff.1 (range_le_decomp S q hd)

variable (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]

lemma exists_not_mem (x : Γ) : ∃ y : ↥(levelField K L hKL), algebraMap ↥(levelField K L hKL) Qbar y ∉ x • A S q :=
  ⟨((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL)))⁻¹, by
    rw [map_inv₀, map_natCast]
    exact inv_natCast_not_mem (qprime S q) ((liesOverPrime_smul_iff _ x _).2 (A_lies S q))⟩

noncomputable def e₀ (x : Γ) : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) :=
  (NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one ↥(levelField K L hKL) (algebraMap ↥(levelField K L hKL) Qbar) (x • A S q)
    (exists_not_mem S q K L hKL x)).exists.choose

lemma e₀_spec (x : Γ) (y : ↥(levelField K L hKL)) : algebraMap ↥(levelField K L hKL) Qbar y ∈ x • A S q ↔ (e₀ S q K L hKL x).valuation ↥(levelField K L hKL) y ≤ 1 :=
  (NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one ↥(levelField K L hKL) (algebraMap ↥(levelField K L hKL) Qbar) (x • A S q)
    (exists_not_mem S q K L hKL x)).exists.choose_spec y

lemma e₀_unique (x : Γ) (v : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)))
    (hv : ∀ y : ↥(levelField K L hKL), algebraMap ↥(levelField K L hKL) Qbar y ∈ x • A S q ↔ v.valuation ↥(levelField K L hKL) y ≤ 1) : v = e₀ S q K L hKL x :=
  (NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one ↥(levelField K L hKL) (algebraMap ↥(levelField K L hKL) Qbar) (x • A S q)
    (exists_not_mem S q K L hKL x)).unique hv (e₀_spec S q K L hKL x)

lemma e₀_eq_of_smul_eq {x₁ x₂ : Γ} (h : x₁ • A S q = x₂ • A S q) : e₀ S q K L hKL x₁ = e₀ S q K L hKL x₂ :=
  (e₀_unique S q K L hKL x₂ _ (fun y => by rw [← h]; exact e₀_spec S q K L hKL x₁ y))

lemma e₀_mul_of_mem_range (x : Γ) {d : Γ} (hd : d ∈ (extArithLoc S (Sum.inr q)).range) :
    e₀ S q K L hKL (x * d) = e₀ S q K L hKL x :=
  e₀_eq_of_smul_eq S q K L hKL (by rw [mul_smul, smul_A_eq_of_mem_range S q hd])

lemma e₀_mul_of_mem_fixing (x : Γ) {s : Γ} (hs : s ∈ L.fixingSubgroup) :
    e₀ S q K L hKL (s * x) = e₀ S q K L hKL x := by
  symm
  apply e₀_unique
  intro y
  rw [← e₀_spec, mul_smul, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have : s⁻¹ • (algebraMap ↥(levelField K L hKL) Qbar y) = algebraMap ↥(levelField K L hKL) Qbar y :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 (L.fixingSubgroup.inv_mem hs) _
      ((IntermediateField.mem_extendScalars hKL).1 y.2)
  rw [this]

variable [Normal ↥K ↥(levelField K L hKL)]

lemma e₀_gamma (γ : ↥K.fixingSubgroup) (x : Γ) :
    e₀ S q K L hKL ((γ : Γ) * x) = levelGal K L hKL γ • e₀ S q K L hKL x := by
  symm
  apply e₀_unique
  intro y
  have h1 : (levelGal K L hKL γ • e₀ S q K L hKL x).valuation ↥(levelField K L hKL) y =
      (e₀ S q K L hKL x).valuation ↥(levelField K L hKL) ((levelGal K L hKL γ)⁻¹ y) := by
    conv_lhs => rw [← show (levelGal K L hKL γ) ((levelGal K L hKL γ)⁻¹ y) = y from AlgEquiv.apply_symm_apply _ y]
    exact NumberField.PlaceTransport.valuation_smul_apply _ _ _
  have h2 : algebraMap ↥(levelField K L hKL) Qbar ((levelGal K L hKL γ)⁻¹ y) = (γ : Γ)⁻¹ • algebraMap ↥(levelField K L hKL) Qbar y := by
    rw [← map_inv]
    exact levelGal_apply_coe K L hKL γ⁻¹ y
  rw [h1, ← e₀_spec, h2, mul_smul, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]

end PlacesF
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"

namespace PlacesF

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section OverQ
variable {q : ℕ} (hq : q.Prime) (A : ValuationSubring Qbar) (hA : A.LiesOverPrime q)

include hq hA in

lemma natCast_mem_nonunits_iff (n : ℕ) : (n : Qbar) ∈ A.nonunits ↔ q ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hcop : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
    obtain ⟨aq, hAq⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hA
    obtain ⟨an, hAn⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hn
    have h1 : ((q.gcdA n * q + q.gcdB n * n : ℤ) : Qbar) = 1 := by
      have := Nat.gcd_eq_gcd_ab q n
      rw [hcop.gcd_eq_one] at this
      push_cast at this
      rw [show (q.gcdA n * q + q.gcdB n * n : ℤ) = 1 by linarith]
      simp
    have hmem : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have e1 : (1 : A) =
          ⟨(q.gcdA n : ℤ), intCast_mem A _⟩ * ⟨(q : Qbar), aq⟩ + ⟨(q.gcdB n : ℤ), intCast_mem A _⟩ * ⟨(n : Qbar), an⟩ := by
        apply Subtype.ext
        show (1 : Qbar) = (q.gcdA n : ℤ) * (q : Qbar) + (q.gcdB n : ℤ) * (n : Qbar)
        rw [← h1]; push_cast; ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hAq) (Ideal.mul_mem_left _ _ hAn)
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem isUnit_one)
  · rintro ⟨m, rfl⟩
    rw [Nat.cast_mul, ValuationSubring.mem_nonunits_iff, map_mul]
    have h1 : A.valuation (q : Qbar) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
    have h2 : A.valuation (m : Qbar) ≤ 1 := (A.valuation_le_one_iff _).2 (natCast_mem A m)
    calc A.valuation (q : Qbar) * A.valuation (m : Qbar) ≤ A.valuation (q : Qbar) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact h1

include hq hA in
lemma valuation_natCast_eq_one_iff {n : ℕ} (hn : n ≠ 0) : A.valuation (n : Qbar) = 1 ↔ ¬ q ∣ n := by
  rw [← natCast_mem_nonunits_iff hq A hA, ValuationSubring.mem_nonunits_iff, not_lt]
  constructor
  · intro h; rw [h]
  · intro h; exact le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A n)) h

include hq hA in
lemma valuation_intCast_eq_one_iff {z : ℤ} (hz : z ≠ 0) : A.valuation (z : Qbar) = 1 ↔ ¬ q ∣ z.natAbs := by
  rw [← valuation_natCast_eq_one_iff hq A hA (Int.natAbs_ne_zero.2 hz)]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]; rw [Int.cast_natCast]
  · conv_lhs => rw [h]; rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]

include hq hA in

lemma ratCast_mem_iff (x : ℚ) : (x : Qbar) ∈ A ↔ ¬ q ∣ x.den := by
  rw [← A.valuation_le_one_iff, Rat.cast_def, map_div₀]
  have hden0 : (x.den : Qbar) ≠ 0 := Nat.cast_ne_zero.2 x.den_ne_zero
  have hvden : 0 < A.valuation (x.den : Qbar) := (Valuation.pos_iff _).2 hden0
  by_cases hqd : q ∣ x.den
  ·
    simp only [hqd, not_true_eq_false, iff_false, not_le]
    have hnum0 : x.num ≠ 0 := by
      intro h0
      have : x = 0 := Rat.zero_iff_num_zero.2 h0
      rw [this] at hqd
      simp at hqd
      exact hq.one_lt.ne' hqd
    have hcop : Nat.Coprime x.num.natAbs x.den := x.reduced
    have hnum : ¬ q ∣ x.num.natAbs := fun h =>
      hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h (Nat.Coprime.coprime_dvd_right hqd hcop)) (dvd_refl q))
    rw [(valuation_intCast_eq_one_iff hq A hA hnum0).2 hnum, one_div, one_lt_inv₀ hvden]
    exact lt_of_le_of_ne ((A.valuation_le_one_iff _).2 (natCast_mem A _))
      (fun h => hqd |> ((valuation_natCast_eq_one_iff hq A hA x.den_ne_zero).1 h))
  · simp only [hqd, not_false_eq_true, iff_true]
    rw [(valuation_natCast_eq_one_iff hq A hA x.den_ne_zero).2 hqd, div_one]
    exact (A.valuation_le_one_iff _).2 (intCast_mem A _)

end OverQ
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"
end PlacesF
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"

namespace PlacesF

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma exists_smul_eq_of_liesOverPrime' {q : ℕ} (hq : q.Prime) (A B : ValuationSubring Qbar)
    (hA : A.LiesOverPrime q) (hB : B.LiesOverPrime q) : ∃ g : Γ, g • A = B := by
  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite
    (A.comap (algebraMap ℚ Qbar)) A B (fun x => Iff.rfl)
    (fun x => by
      show algebraMap ℚ Qbar x ∈ B ↔ algebraMap ℚ Qbar x ∈ A
      rw [eq_ratCast, ratCast_mem_iff hq B hB, ratCast_mem_iff hq A hA])
  refine ⟨σ, SetLike.ext fun z => ?_⟩
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hσ (σ⁻¹ • z)]
  show σ (σ.symm z) ∈ B ↔ z ∈ B
  rw [AlgEquiv.apply_symm_apply]

end PlacesF
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"

namespace PlacesF

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (q : ↥S) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]

abbrev X : Type := Γ ⧸ (extArithLoc S (Sum.inr q)).range

noncomputable def placeX : X S q → HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) :=
  Quotient.lift (e₀ S q K L hKL) fun a b hab => by
    have hab' : a⁻¹ * b ∈ (extArithLoc S (Sum.inr q)).range := QuotientGroup.leftRel_apply.1 hab
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb, e₀_mul_of_mem_range S q K L hKL a hab']

lemma placeX_mk (x : Γ) : placeX S q K L hKL (x : X S q) = e₀ S q K L hKL x := rfl

noncomputable def placeQ : placesAbove L S (Sum.inr q) → HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) :=
  Quotient.lift (placeX S q K L hKL) fun a b hab => by
    change (MulAction.orbitRel ↥L.fixingSubgroup (X S q)) a b at hab
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
    obtain ⟨s, rfl⟩ := hab
    induction b using QuotientGroup.induction_on with
    | H x =>
      show placeX S q K L hKL ((((s : Γ) * x : Γ) : X S q)) = placeX S q K L hKL (x : X S q)
      rw [placeX_mk, placeX_mk, e₀_mul_of_mem_fixing S q K L hKL x s.2]

lemma placeQ_mk_mk (x : Γ) : placeQ S q K L hKL (Quotient.mk'' (x : X S q)) = e₀ S q K L hKL x := rfl

lemma placeQ_smul (hnorm : IsNormalLevel K L) [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup)
    (c : placesAbove L S (Sum.inr q)) :
    placeQ S q K L hKL ((orbitQuotientAction K L hnorm (X S q)).smul γ c) = levelGal K L hKL γ • placeQ S q K L hKL c := by
  induction c using Quotient.inductionOn' with
  | h c =>
    induction c using QuotientGroup.induction_on with
    | H x =>
      show placeQ S q K L hKL (Quotient.mk'' ((((γ : Γ) * x : Γ) : X S q))) = _
      rw [placeQ_mk_mk, placeQ_mk_mk, e₀_gamma]

scoped instance isGaloisK : IsGalois ↥K Qbar := IsGalois.tower_top_intermediateField K

scoped instance isGaloisL' : IsGalois ↥(levelField K L hKL) Qbar := IsGalois.tower_top_intermediateField (levelField K L hKL)

lemma mem_fixing_of_algEquiv (σ : Qbar ≃ₐ[↥(levelField K L hKL)] Qbar) :
    AlgEquiv.ofRingEquiv (f := (σ : Qbar ≃+* Qbar))
        (fun r => by rw [eq_ratCast]; exact map_ratCast (σ : Qbar ≃+* Qbar) r) ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  exact σ.commutes ⟨y, (IntermediateField.mem_extendScalars hKL).2 hy⟩

lemma placeQ_injective : Function.Injective (placeQ S q K L hKL) := by
  intro c₁ c₂ h
  induction c₁ using Quotient.inductionOn' with
  | h c₁ =>
  induction c₂ using Quotient.inductionOn' with
  | h c₂ =>
  induction c₁ using QuotientGroup.induction_on with
  | H x₁ =>
  induction c₂ using QuotientGroup.induction_on with
  | H x₂ =>
  rw [placeQ_mk_mk, placeQ_mk_mk] at h

  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite
    ((x₁ • A S q).comap (algebraMap ↥(levelField K L hKL) Qbar)) (x₁ • A S q) (x₂ • A S q)
    (fun y => Iff.rfl)
    (fun y => by
      show _ ↔ algebraMap ↥(levelField K L hKL) Qbar y ∈ x₁ • A S q
      rw [e₀_spec, e₀_spec, h])
  set s : Γ := AlgEquiv.ofRingEquiv (f := (σ : Qbar ≃+* Qbar))
    (fun r => by rw [eq_ratCast]; exact map_ratCast (σ : Qbar ≃+* Qbar) r) with hs_def
  have hs : s ∈ L.fixingSubgroup := mem_fixing_of_algEquiv K L hKL σ
  have hsA : s • (x₁ • A S q) = x₂ • A S q := by
    apply SetLike.ext
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hσ (s⁻¹ • z)]
    show σ (s.symm z) ∈ x₂ • A S q ↔ _
    rw [show σ (s.symm z) = z from AlgEquiv.apply_symm_apply s z]

  have hd : x₁⁻¹ * s⁻¹ * x₂ ∈ (A S q).decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hsA, inv_smul_smul, inv_smul_smul]
  obtain ⟨s', hs', r, hr, hxd⟩ := exists_mem_mul_eq_of_mem_closure L _ x₁ (x₁⁻¹ * s⁻¹ * x₂)
    (decomp_le_closure S q hd)

  have hx₂ : x₂ = (s * s') * x₁ * r := by
    have : x₂ = s * (x₁ * (x₁⁻¹ * s⁻¹ * x₂)) := by group
    rw [this, hxd]; group
  apply Quotient.sound'
  change (MulAction.orbitRel ↥L.fixingSubgroup (X S q)) (x₁ : X S q) (x₂ : X S q)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨⟨(s * s')⁻¹, L.fixingSubgroup.inv_mem (L.fixingSubgroup.mul_mem hs hs')⟩, ?_⟩
  show ((((s * s')⁻¹ * x₂ : Γ)) : X S q) = (x₁ : X S q)
  rw [hx₂, show (s * s')⁻¹ * ((s * s') * x₁ * r) = x₁ * r by group]
  exact QuotientGroup.mk_mul_of_mem x₁ hr

lemma valuation_natCast_lt_one (x : Γ) :
    (e₀ S q K L hKL x).valuation ↥(levelField K L hKL) ((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL))) < 1 := by
  have hq0 : ((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL))) ≠ 0 := Nat.cast_ne_zero.2 (qprime S q).ne_zero
  have h1 : ¬ (e₀ S q K L hKL x).valuation ↥(levelField K L hKL) ((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL)))⁻¹ ≤ 1 := by
    rw [← e₀_spec, map_inv₀, map_natCast]
    exact inv_natCast_not_mem (qprime S q) ((liesOverPrime_smul_iff _ x _).2 (A_lies S q))
  rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).2 hq0), not_le] at h1
  exact h1

lemma natCast_mem_asIdeal (x : Γ) :
    ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ (e₀ S q K L hKL x).asIdeal := by
  rw [← (e₀ S q K L hKL x).valuation_lt_one_iff_mem (K := ↥(levelField K L hKL))]
  change (e₀ S q K L hKL x).valuation ↥(levelField K L hKL)
    (algebraMap (𝓞 ↥(levelField K L hKL)) ↥(levelField K L hKL) ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)))) < 1
  rw [map_natCast]
  exact valuation_natCast_lt_one S q K L hKL x

lemma valuation_natCast_lt_one_of_mem (w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)))
    (hw : ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal) :
    w.valuation ↥(levelField K L hKL) ((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL))) < 1 := by
  have := (w.valuation_lt_one_iff_mem (K := ↥(levelField K L hKL)) _).2 hw
  change w.valuation ↥(levelField K L hKL)
    (algebraMap (𝓞 ↥(levelField K L hKL)) ↥(levelField K L hKL) ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)))) < 1 at this
  rwa [map_natCast] at this

lemma liesOverPrime_of_forall (w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)))
    (hw : ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal) (B : ValuationSubring Qbar)
    (hB : ∀ y : ↥(levelField K L hKL), algebraMap ↥(levelField K L hKL) Qbar y ∈ B ↔ w.valuation ↥(levelField K L hKL) y ≤ 1) :
    B.LiesOverPrime ((q : Nat.Primes) : ℕ) := by
  rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff_or]
  right
  have hq0 : ((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL))) ≠ 0 := Nat.cast_ne_zero.2 (qprime S q).ne_zero
  have h1 : ((((q : Nat.Primes) : ℕ) : Qbar))⁻¹ =
      algebraMap ↥(levelField K L hKL) Qbar (((((q : Nat.Primes) : ℕ) : ↥(levelField K L hKL)))⁻¹) := by
    rw [map_inv₀, map_natCast]
  rw [h1, hB, map_inv₀, not_le, one_lt_inv₀ ((Valuation.pos_iff _).2 hq0)]
  exact valuation_natCast_lt_one_of_mem S q K L hKL w hw

lemma exists_e₀_eq (w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)))
    (hw : ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal) : ∃ g : Γ, e₀ S q K L hKL g = w := by
  obtain ⟨B, hB⟩ := NumberField.exists_valuationSubring_forall_map_mem_iff_valuation_le_one ↥(levelField K L hKL)
    (algebraMap ↥(levelField K L hKL) Qbar) w
  have hBq : B.LiesOverPrime ((q : Nat.Primes) : ℕ) := liesOverPrime_of_forall S q K L hKL w hw B hB
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨qprime S q⟩
  obtain ⟨g, hg⟩ := exists_smul_eq_of_liesOverPrime' (qprime S q) (A S q) B (A_lies S q) hBq
  refine ⟨g, (e₀_unique S q K L hKL g w (fun y => ?_)).symm⟩
  rw [← hB y, hg]

lemma range_placeQ : Set.range (placeQ S q K L hKL) =
    {w | ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal} := by
  ext w
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quotient.inductionOn' with
    | h c =>
      induction c using QuotientGroup.induction_on with
      | H x => exact natCast_mem_asIdeal S q K L hKL x
  · intro hw
    obtain ⟨g, hg⟩ := exists_e₀_eq S q K L hKL w hw
    exact ⟨Quotient.mk'' (g : X S q), hg⟩

end PlacesF
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.PlacesF"

open PlacesF in
theorem solution
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (q : ↥S) :
    ∃ e : placesAbove L S (Sum.inr q) → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField K L hKL)),
      Function.Injective e ∧
      Set.range e = {w | ((((q : Nat.Primes) : ℕ) : NumberField.RingOfIntegers ↥(levelField K L hKL))) ∈ w.asIdeal} ∧
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)),
        e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ x) =
          levelGal K L hKL γ • e x :=
  ⟨placeQ S q K L hKL, placeQ_injective S q K L hKL, range_placeQ S q K L hKL, placeQ_smul S q K L hKL hnorm⟩

end S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum
end P2MW
export P2MW.S_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum (solution)
