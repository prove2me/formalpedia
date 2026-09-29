-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_layerConstants_uniformizers_completions_of_constantsTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/8d6a7af8-c2aa-5198-b31d-240781909340

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
import Theorems.Thm_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_layerConstants_uniformizers_completions_of_constantsTower

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace LayerDataAux

theorem isUnit_iff_inv_mem {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubringClass S F]
    (s : S) (a : F) (ha : a ∈ s) :
    IsUnit (⟨a, ha⟩ : s) ↔ a ≠ 0 ∧ a⁻¹ ∈ s := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : a * ((↑(u⁻¹) : s) : F) = 1 := by
      have h := congrArg (fun z : s => (z : F)) u.mul_inv
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
      rwa [hu] at h
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨ha0, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  · rintro ⟨ha0, hai⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hai⟩, Subtype.ext (by simp [ha0])⟩

end LayerDataAux

open LayerDataAux in

theorem solution
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))
    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (n₀ : ι) (hn₀ : ∀ n, K n₀ ≤ K n)
    (πt : AlgebraicClosure ℚ) (hπt : πt ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπA : πt ∈ A)

    (htame : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 → ∀ x : ↥(K n₀), τ (x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) :
    ∀ (E₀ : ℕ), 1 ≤ E₀ → ∀ (w₀ : ℕ),
      (∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧ π₀ ^ E₀ = ϖt ^ w₀ * v) →
    ∃ (C' : ι → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
      (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
      (ϖ' : ∀ l, ↥(C' l))
      (Wc : ι → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
      (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
      (π : ∀ l, Wc l) (eL : ι → ℕ) (jc : ∀ l, ↥(C' l) →+* Wc l),

      (∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l ↔ c ∈ A ∧ c ∈ Set.range (fun x : ↥(K l) => (x : AlgebraicClosure ℚ))) ∧

      (∀ (l : ι) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
      (∀ l, C' n₀ ≤ C' l) ∧
      ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
      (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' n₀) a) ∧
      (∀ l, Irreducible (π l)) ∧ (∀ l, 1 ≤ eL l) ∧

      (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
        τ ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) = ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ)) ∧

      (∃ w : ℕ, 1 ≤ w ∧ ∃ v : (↥A)ˣ,
        (⟨((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ), hC'A n₀ _ (ϖ' n₀).2⟩ : ↥A) ^ (eL n₀ * E₀) = (v : ↥A) * ⟨πt, hπA⟩ ^ w) ∧

      (∀ l, ∃ v : AlgebraicClosure ℚ, v ∈ C' l ∧ v⁻¹ ∈ C' l ∧ (π₀ : AlgebraicClosure ℚ) = v * ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ^ eL l) ∧
      (∀ l, jc l (ϖ' l) = π l) ∧
      (∀ (l : ι) (n : ℕ) (c : ↥(C' l)), jc l c ∈ Ideal.span {π l ^ n} → c ∈ Ideal.span {ϖ' l ^ n}) ∧
      (∀ (l : ι) (n : ℕ) (w : Wc l), ∃ c : ↥(C' l), w - jc l c ∈ Ideal.span {π l ^ n}) := by
  intro E₀ hE₀ w₀ hmod
  classical
  haveI := hdvr
  set A₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) with hA₀def

  have hπ0ne : (π₀ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h' : π₀ = 0 := by exact_mod_cast h
    apply IsDiscreteValuationRing.not_a_field ↥A₀
    rw [hunif, Ideal.span_singleton_eq_bot]
    exact Subtype.ext h'
  have hπ0k : (π₀ : ↥k₀) ≠ 0 := fun h => hπ0ne (by simp [h])
  have hπ0notunit : ¬ IsUnit (⟨π₀, hπ⟩ : ↥A₀) := by
    have hm : (⟨π₀, hπ⟩ : ↥A₀) ∈ maximalIdeal ↥A₀ := by
      rw [hunif]; exact Ideal.mem_span_singleton_self _
    exact (mem_nonunits_iff).1 ((mem_maximalIdeal _).1 hm)
  have hπ0inv : (π₀ : AlgebraicClosure ℚ)⁻¹ ∉ A := by
    intro hmem
    apply hπ0notunit
    have hmem' : (π₀⁻¹ : ↥k₀) ∈ A₀ := by
      rw [hA₀def, ValuationSubring.mem_comap]
      simpa using hmem
    refine isUnit_iff_exists_inv.2 ⟨⟨π₀⁻¹, hmem'⟩, ?_⟩
    apply Subtype.ext
    simp [hπ0k]

  have hqP : q.Prime := Fact.out
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hqP.ne_zero
  have hN : q ^ 2 - 1 ≠ 0 := by
    have h2 := hqP.two_le
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  have hπt0 : πt ≠ 0 := fun h => hq0 (by rw [← hπt, h, zero_pow hN])
  obtain ⟨uϖ, huϖ, hϖteq⟩ := hϖt
  have hϖt0 : (ϖt : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    rw [h, zero_pow hN] at hϖteq
    have : ((uϖ : ↥A) : AlgebraicClosure ℚ) = 0 := by
      rcases mul_eq_zero.1 hϖteq.symm with h' | h'
      · exact absurd h' hq0
      · exact h'
    exact huϖ.ne_zero (Subtype.ext this)
  set r : AlgebraicClosure ℚ := (ϖt : AlgebraicClosure ℚ) * πt⁻¹ with hr
  have hr0 : r ≠ 0 := mul_ne_zero hϖt0 (inv_ne_zero hπt0)
  have hrN : r ^ (q ^ 2 - 1) = ((uϖ : ↥A) : AlgebraicClosure ℚ) := by
    rw [hr, mul_pow, inv_pow, hϖteq, hπt]
    field_simp
  have hrA : r ∈ A ∧ r⁻¹ ∈ A := by
    rcases A.mem_or_inv_mem r with h | h
    · have hu : IsUnit (⟨r, h⟩ : ↥A) := by
        rw [← isUnit_pow_iff hN]
        have : (⟨r, h⟩ : ↥A) ^ (q ^ 2 - 1) = uϖ := Subtype.ext (by simp [hrN])
        rw [this]; exact huϖ
      exact ⟨h, ((isUnit_iff_inv_mem A r h).1 hu).2⟩
    · have hu : IsUnit (⟨r⁻¹, h⟩ : ↥A) := by
        rw [← isUnit_pow_iff hN]
        refine IsUnit.of_mul_eq_one uϖ ?_
        apply Subtype.ext
        simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← hrN, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hr0)]
      have := ((isUnit_iff_inv_mem A r⁻¹ h).1 hu).2
      rw [inv_inv] at this
      exact ⟨this, h⟩

  obtain ⟨v, hvA, hvinvA, hπE⟩ := hmod
  have hvinvA' : ((v : AlgebraicClosure ℚ))⁻¹ ∈ A := by simpa using hvinvA
  have hπE' : (π₀ : AlgebraicClosure ℚ) ^ E₀ = (ϖt : AlgebraicClosure ℚ) ^ w₀ * (v : AlgebraicClosure ℚ) := by
    have := congrArg (fun z : ↥k₀ => (z : AlgebraicClosure ℚ)) hπE
    simpa using this
  have hv0 : (v : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hπE'
    exact hπ0ne (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 hE₀) |>.1 hπE')
  have hw₀ : 1 ≤ w₀ := by
    rcases Nat.eq_zero_or_pos w₀ with h | h
    · exfalso
      rw [h, pow_zero, one_mul] at hπE'
      apply hπ0inv
      have hu : IsUnit (⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ : ↥A) := by
        rw [← isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hE₀)]
        have : (⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ : ↥A) ^ E₀ = ⟨(v : AlgebraicClosure ℚ), hvA⟩ :=
          Subtype.ext (by simp [hπE'])
        rw [this]
        exact (isUnit_iff_inv_mem A _ hvA).2 ⟨hv0, hvinvA'⟩
      exact ((isUnit_iff_inv_mem A _ hπ).1 hu).2
    · exact h

  have hDVRAn : ∀ l, IsDiscreteValuationRing ↥(An l) := by
    intro l
    letI : Algebra ↥A₀ ↥(K l) := ((algebraMap ↥k₀ ↥(K l)).comp (algebraMap ↥A₀ ↥k₀)).toAlgebra
    haveI : IsScalarTower ↥A₀ ↥k₀ ↥(K l) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Module.Finite ↥k₀ ↥(K l) := hKfin l
    refine ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
      (A := ↥A₀) (K := ↥k₀) (An l) ?_ ?_
    · intro a
      rw [hAn]
      show ((algebraMap ↥k₀ ↥(K l) (a : ↥k₀) : ↥(K l)) : AlgebraicClosure ℚ) ∈ A
      rw [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply]
      exact (ValuationSubring.mem_comap).1 a.2
    · intro htop
      apply hπ0inv
      have hmem : (algebraMap ↥k₀ ↥(K l) π₀⁻¹) ∈ An l := by
        rw [htop]; exact ValuationSubring.mem_top _
      have := (hAn l _).1 hmem
      rw [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply] at this
      simpa using this

  let f : ∀ l, ↥(K l) →+* AlgebraicClosure ℚ := fun l => SubringClass.subtype (K l)
  have hfinj : ∀ l, Function.Injective (f l) := fun l => Subtype.val_injective
  let C' : ι → Subring (AlgebraicClosure ℚ) := fun l => (An l).toSubring.map (f l)
  have hmemC : ∀ (l : ι) (c : AlgebraicClosure ℚ),
      c ∈ C' l ↔ c ∈ A ∧ c ∈ Set.range (fun x : ↥(K l) => (x : AlgebraicClosure ℚ)) := by
    intro l c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hAn l x).1 hx, x, rfl⟩
    · rintro ⟨hcA, x, rfl⟩
      exact ⟨x, (hAn l x).2 hcA, rfl⟩
  have hC'A : ∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A :=
    fun l c hc => ((hmemC l c).1 hc).1
  have hDVRC : ∀ l, IsDiscreteValuationRing ↥(C' l) := by
    intro l
    haveI : IsDiscreteValuationRing ↥(An l).toSubring := hDVRAn l
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ((An l).toSubring.equivMapOfInjective (f l) (hfinj l))

  have hϖex : ∀ l, ∃ ϖ : ↥(C' l), Irreducible ϖ :=
    fun l => IsDiscreteValuationRing.exists_irreducible _
  choose ϖ' hϖ' using hϖex

  have hπ₀C : ∀ l, (π₀ : AlgebraicClosure ℚ) ∈ C' l :=
    fun l => (hmemC l _).2 ⟨hπ, ⟨algebraMap ↥k₀ ↥(K l) π₀, rfl⟩⟩
  have hram : ∀ l, ∃ (n : ℕ) (u : (↥(C' l))ˣ),
      (⟨(π₀ : AlgebraicClosure ℚ), hπ₀C l⟩ : ↥(C' l)) = u * ϖ' l ^ n :=
    fun l => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (by intro h; exact hπ0ne (congrArg Subtype.val h)) (hϖ' l)
  choose eL uL huL using hram
  have heL : ∀ l, 1 ≤ eL l := by
    intro l
    by_contra hlt
    have h0 : eL l = 0 := by omega
    have h := huL l
    rw [h0, pow_zero, mul_one] at h
    apply hπ0inv
    have hu : IsUnit (⟨(π₀ : AlgebraicClosure ℚ), hπ₀C l⟩ : ↥(C' l)) := by
      rw [h]; exact Units.isUnit _
    exact hC'A l _ ((isUnit_iff_inv_mem (C' l) _ (hπ₀C l)).1 hu).2

  have hcomp := fun l =>
    IsDiscreteValuationRing.exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal ↥(C' l)
  choose Wc iCR iDom iDVR iCpl jc hjloc hmap hdense using hcomp
  have hmW : ∀ l, maximalIdeal (Wc l) = Ideal.span {jc l (ϖ' l)} := by
    intro l
    rw [← hmap l, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (hϖ' l), Ideal.map_span,
      Set.image_singleton]
  have hπirr : ∀ l, Irreducible (jc l (ϖ' l)) :=
    fun l => (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (hmW l)

  have hiso : ∀ (l : ι) (n : ℕ) (c : ↥(C' l)),
      jc l c ∈ Ideal.span {jc l (ϖ' l) ^ n} → c ∈ Ideal.span {ϖ' l ^ n} := by
    intro l n c hc
    by_cases hc0 : c = 0
    · simp [hc0]
    obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 (hϖ' l)
    rw [Ideal.mem_span_singleton, hk]
    suffices hnk : n ≤ k from Dvd.dvd.mul_left (pow_dvd_pow _ hnk) _
    by_contra hlt
    have hlt : k < n := Nat.lt_of_not_le hlt
    have hπ0 : jc l (ϖ' l) ≠ 0 := (hπirr l).ne_zero
    rw [Ideal.mem_span_singleton, hk, map_mul, map_pow] at hc
    have hdvd : jc l (ϖ' l) ^ (k + 1) ∣ jc l ↑u * jc l (ϖ' l) ^ k :=
      (pow_dvd_pow (jc l (ϖ' l)) (by omega)).trans hc
    rw [pow_succ', mul_dvd_mul_iff_right (pow_ne_zero k hπ0)] at hdvd
    exact (hπirr l).not_isUnit (isUnit_of_dvd_unit hdvd (u.isUnit.map (jc l)))

  have hdense' : ∀ (l : ι) (n : ℕ) (w : Wc l), ∃ c : ↥(C' l), w - jc l c ∈ Ideal.span {jc l (ϖ' l) ^ n} := by
    intro l n
    induction n with
    | zero => intro w; exact ⟨0, by simp⟩
    | succ n ih =>
      intro w
      obtain ⟨c, hc⟩ := ih w
      obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 hc
      obtain ⟨a, ha⟩ := hdense l w'
      rw [hmW l] at ha
      obtain ⟨w'', hw''⟩ := Ideal.mem_span_singleton'.1 ha
      refine ⟨c + a * ϖ' l ^ n, Ideal.mem_span_singleton'.2 ⟨w'', ?_⟩⟩
      rw [map_add, map_mul, map_pow, pow_succ]
      linear_combination (jc l (ϖ' l) ^ n) * hw'' + hw'

  have hres' : ∀ (l : ι) (d : ↥(C' l)),
      IsLocalRing.residue ↥A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d' := by
    intro l d
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    have key : IsUnit (⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ : ↥A) ↔ IsUnit d := by
      rw [isUnit_iff_inv_mem A (d : AlgebraicClosure ℚ) (hC'A l d d.2),
        show IsUnit d ↔ IsUnit (⟨(d : AlgebraicClosure ℚ), d.2⟩ : ↥(C' l)) from Iff.rfl,
        isUnit_iff_inv_mem (C' l) (d : AlgebraicClosure ℚ) d.2]
      constructor
      · rintro ⟨h0, hiA⟩
        refine ⟨h0, (hmemC l _).2 ⟨hiA, ?_⟩⟩
        obtain ⟨x, hx⟩ := ((hmemC l _).1 d.2).2
        exact ⟨x⁻¹, by rw [← hx]; simp⟩
      · rintro ⟨h0, hiC⟩
        exact ⟨h0, hC'A l _ hiC⟩
    rw [key, ← mem_nonunits_iff, ← mem_maximalIdeal,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (hϖ' l), Ideal.mem_span_singleton]
    exact Iff.rfl

  have hle : ∀ l, C' n₀ ≤ C' l := by
    intro l c hc
    obtain ⟨hcA, x, rfl⟩ := (hmemC n₀ c).1 hc
    exact (hmemC l _).2 ⟨hcA, ⟨(x : AlgebraicClosure ℚ), hn₀ l x.2⟩, rfl⟩

  have halg : ∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' n₀) a := by
    intro a _
    have hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    have h1 : IsAlgebraic ℚ a := hQalg.isAlgebraic a
    have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).2 h1
    obtain ⟨p, hp0, hpa⟩ := h2
    have hinj : Function.Injective (Int.castRingHom ↥(C' n₀)) := by
      intro x y hxy
      have := congrArg (fun z : ↥(C' n₀) => (z : AlgebraicClosure ℚ)) hxy
      simp only [Int.coe_castRingHom, SubringClass.coe_intCast] at this
      exact_mod_cast this
    refine ⟨p.map (Int.castRingHom ↥(C' n₀)), fun h => hp0 ((Polynomial.map_eq_zero_iff hinj).1 h), ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hpa, Polynomial.aeval_def]
    congr 1

  have hiner : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
      τ ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) = ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) := by
    intro τ hτ h1
    obtain ⟨x, hx⟩ := ((hmemC n₀ _).1 (ϖ' n₀).2).2
    rw [← hx]
    exact htame τ hτ h1 x

  have hramC : ∀ l, ∃ v : AlgebraicClosure ℚ, v ∈ C' l ∧ v⁻¹ ∈ C' l ∧
      (π₀ : AlgebraicClosure ℚ) = v * ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ^ eL l := by
    intro l
    refine ⟨((uL l : ↥(C' l)) : AlgebraicClosure ℚ), (uL l : ↥(C' l)).2, ?_, ?_⟩
    · exact ((isUnit_iff_inv_mem (C' l) _ (uL l : ↥(C' l)).2).1 (uL l).isUnit).2
    · have := congrArg Subtype.val (huL l)
      simpa using this

  have hbase : ∃ w : ℕ, 1 ≤ w ∧ ∃ vv : (↥A)ˣ,
      (⟨((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ), hC'A n₀ _ (ϖ' n₀).2⟩ : ↥A) ^ (eL n₀ * E₀) =
        (vv : ↥A) * ⟨πt, hπA⟩ ^ w := by
    obtain ⟨v₁, hv₁C, hv₁iC, hπ₀eq⟩ := hramC n₀
    have hv₁0 : v₁ ≠ 0 := by
      rintro rfl
      exact hπ0ne (by simpa using hπ₀eq)
    set a : AlgebraicClosure ℚ := (v : AlgebraicClosure ℚ) * (v₁⁻¹) ^ E₀ * r ^ w₀ with ha
    have haA : a ∈ A := mul_mem (mul_mem hvA (pow_mem (hC'A _ _ hv₁iC) _)) (pow_mem hrA.1 _)
    have hane : a ≠ 0 := by
      rw [ha]
      exact mul_ne_zero (mul_ne_zero hv0 (pow_ne_zero _ (inv_ne_zero hv₁0))) (pow_ne_zero _ hr0)
    have hainv : a⁻¹ = ((v : AlgebraicClosure ℚ))⁻¹ * v₁ ^ E₀ * r⁻¹ ^ w₀ := by
      rw [ha, mul_inv, mul_inv, inv_pow, inv_pow, inv_inv]
    have haiA : a⁻¹ ∈ A := by
      rw [hainv]
      exact mul_mem (mul_mem hvinvA' (pow_mem (hC'A _ _ hv₁C) _)) (pow_mem hrA.2 _)
    obtain ⟨ua, hua⟩ := (isUnit_iff_inv_mem A a haA).2 ⟨hane, haiA⟩
    refine ⟨w₀, hw₀, ua, ?_⟩
    apply Subtype.ext
    rw [hua]
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul]
    have hϖ'eq : ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ^ eL n₀ = (π₀ : AlgebraicClosure ℚ) * v₁⁻¹ := by
      rw [hπ₀eq]; field_simp
    have hrw : r ^ w₀ * πt ^ w₀ = (ϖt : AlgebraicClosure ℚ) ^ w₀ := by
      rw [hr, mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπt0), mul_one]
    calc ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ^ (eL n₀ * E₀)
        = (((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ^ eL n₀) ^ E₀ := pow_mul _ _ _
      _ = ((π₀ : AlgebraicClosure ℚ) * v₁⁻¹) ^ E₀ := by rw [hϖ'eq]
      _ = (π₀ : AlgebraicClosure ℚ) ^ E₀ * (v₁⁻¹) ^ E₀ := mul_pow _ _ _
      _ = (ϖt : AlgebraicClosure ℚ) ^ w₀ * (v : AlgebraicClosure ℚ) * (v₁⁻¹) ^ E₀ := by rw [hπE']
      _ = (v : AlgebraicClosure ℚ) * (v₁⁻¹) ^ E₀ * (r ^ w₀ * πt ^ w₀) := by rw [hrw]; ring
      _ = a * πt ^ w₀ := by rw [ha]; ring

  refine ⟨C', hC'A, fun l => inferInstance, hDVRC, ϖ', Wc, iCR, iDom, iDVR, iCpl, fun l => jc l (ϖ' l), eL, jc,
    hmemC, hres', hle, ?_, halg, hπirr, heL, hiner, hbase, hramC, fun l => rfl, hiso, hdense'⟩
  intro h
  exact (hϖ' n₀).ne_zero (by exact_mod_cast h)

end S_ModularCurve_FullLevel_exists_layerConstants_uniformizers_completions_of_constantsTower
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_layerConstants_uniformizers_completions_of_constantsTower (solution)
