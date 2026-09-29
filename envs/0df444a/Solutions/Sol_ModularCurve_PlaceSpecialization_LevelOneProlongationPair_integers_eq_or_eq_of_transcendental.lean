-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b3e177f1-8fa1-5824-a482-ed1a4a96ab3e

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_ne_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_transcendental
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~dedekindPsi_prime"

namespace Ws25
namespace E2

open ModularCurve.PlaceSpecialization IntermediateField Polynomial

section Generators

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

def gens : Set (LaurentSeries L) := ⇑(coeffEmb L) '' divisorExpansions N

theorem adjoin_gens_le : adjoin L (gens L N) ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
  change adjoin L (gens L N) ≤ adjoin L _
  refine adjoin.mono L _ _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, IntermediateField.subset_adjoin ℚ _ hx, rfl⟩

theorem laurentBaseChange_le_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) ≤ adjoin L (gens L N) := by
  change adjoin L _ ≤ adjoin L (gens L N)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gens L N)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gens L N)).algebraMap_mem _
  · exact IntermediateField.subset_adjoin L _ ⟨z, hz, rfl⟩

theorem laurentBaseChange_eq_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) = adjoin L (gens L N) :=
  le_antisymm (laurentBaseChange_le_adjoin_gens L N) (adjoin_gens_le L N)

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gens L N)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (coeffEmb L (qExpand ℚ d jq)).coeff n = (m : L) := by
        rw [coeffEmb_coeff]
        by_cases hdn : (d : ℤ) ∣ n
        · obtain ⟨n', rfl⟩ := hdn
          refine ⟨(jqModC ℤ).coeff n', ?_⟩
          rw [qExpand_coeff_mul, ← jqModC_rat, coeff_jqModC_eq_intCast, map_intCast]
        · exact ⟨0, by rw [qExpand_coeff_of_not_dvd _ _ hdn, map_zero, Int.cast_zero]⟩
      rw [hm, ← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | algebraMap a =>
      refine ⟨Submodule.span ℤ {a}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
      split_ifs
      · exact Submodule.subset_span rfl
      · exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | mul x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ * M₂, hM₁.mul hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_mul]
      exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (h₁ _) (h₂ _)

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  rw [coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]

theorem gens_eq_divisorExpansionsC : gens L N = divisorExpansionsC L N := by
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩
    exact ⟨d, hd, hdN, coeffEmb_qExpand_jq L d⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact ⟨_, ⟨d, hd, hdN, rfl⟩, coeffEmb_qExpand_jq L d⟩

theorem laurentBaseChange_eq_fullC :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldFullC L N := by
  rw [laurentBaseChange_eq_adjoin_gens, gens_eq_divisorExpansionsC]; rfl

theorem finrank_adjoin_transport {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  rw [dedekindPsi, Nat.Prime.divisors hp]
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton,
    if_pos hp.squarefree, Finset.sum_insert (by simpa using h1p), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos, add_comm]

end Generators

section Orders

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem dvd_order_of_mem_range_qExpand {x : LaurentSeries K}
    (hx : x ∈ Set.range (qExpand K N)) (h0 : x ≠ 0) : (N : ℤ) ∣ x.order := by
  by_contra hnd
  obtain ⟨y, rfl⟩ := hx
  exact (HahnSeries.coeff_order_eq_zero.not.mpr h0) (qExpand_coeff_of_not_dvd (R := K) (N := N) y hnd)

theorem order_jqModC_pow (b : ℕ) : (jqModC K ^ b).order = -(b : ℤ) := by
  have h1 : (jqModC K ^ b).coeff (-(b : ℤ)) ≠ 0 := by
    rw [ModularCurve.coeff_jqModC_pow_self]; exact one_ne_zero
  have h0 : jqModC K ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  have hle : (jqModC K ^ b).order ≤ -(b : ℤ) := HahnSeries.order_le_of_coeff_ne_zero h1
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd (ModularCurve.coeff_jqModC_pow_of_lt K hlt) (HahnSeries.coeff_order_eq_zero.not.mpr h0)
  · exact heq

theorem order_mul_pow_jqModC {c : LaurentSeries K} (hc : c ≠ 0) (b : ℕ) :
    (c * jqModC K ^ b).order = c.order - b := by
  have h0 : jqModC K ^ b ≠ 0 := pow_ne_zero _ (jqModC_ne_zero_of_nontrivial K)
  rw [HahnSeries.order_mul_of_ne_zero (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hc)
    (HahnSeries.leadingCoeff_ne_zero.mpr h0)), order_jqModC_pow, sub_eq_add_neg]

theorem eq_zero_of_sum_mul_pow_jqModC_eq_zero (c : Fin N → LaurentSeries K)
    (hc : ∀ i, c i ∈ Set.range (qExpand K N))
    (h : ∑ i, c i * jqModC K ^ (i : ℕ) = 0) : ∀ i, c i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  classical

  have hTne : (Finset.univ.filter fun i : Fin N => c i ≠ 0).Nonempty :=
    ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩⟩

  have hinj : ∀ i i' : Fin N, c i ≠ 0 → c i' ≠ 0 →
      (c i * jqModC K ^ (i : ℕ)).order = (c i' * jqModC K ^ (i' : ℕ)).order → i = i' := by
    intro i i' hi hi' he
    rw [order_mul_pow_jqModC K hi, order_mul_pow_jqModC K hi'] at he
    obtain ⟨a, ha⟩ := dvd_order_of_mem_range_qExpand K N (hc i) hi
    obtain ⟨a', ha'⟩ := dvd_order_of_mem_range_qExpand K N (hc i') hi'
    rw [ha, ha'] at he
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmod : ((i : ℕ) : ℤ) % N = ((i' : ℕ) : ℤ) % N := by
      have : ((i : ℕ) : ℤ) = ((i' : ℕ) : ℤ) + N * (a - a') := by linear_combination -he
      rw [this, Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i'.2)] at hmod
    exact Fin.ext (by exact_mod_cast hmod)

  obtain ⟨i₀, hi₀T, hmin⟩ := (Finset.univ.filter fun i : Fin N => c i ≠ 0).exists_min_image
    (fun i => (c i * jqModC K ^ (i : ℕ)).order) hTne
  have hi₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
  have ht₀ : c i₀ * jqModC K ^ (i₀ : ℕ) ≠ 0 :=
    mul_ne_zero hi₀ (pow_ne_zero _ (jqModC_ne_zero_of_nontrivial K))

  have hcoeff : (∑ i, c i * jqModC K ^ (i : ℕ)).coeff (c i₀ * jqModC K ^ (i₀ : ℕ)).order
      = (c i₀ * jqModC K ^ (i₀ : ℕ)).coeff (c i₀ * jqModC K ^ (i₀ : ℕ)).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases hci : c i = 0
    · rw [hci, zero_mul, HahnSeries.coeff_zero]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hle := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩)
      exact lt_of_le_of_ne hle fun he => hi (hinj i i₀ hci hi₀ he.symm)
  rw [h, HahnSeries.coeff_zero] at hcoeff
  exact (HahnSeries.coeff_order_eq_zero.not.mpr ht₀) hcoeff.symm

theorem linearIndependent_pow (E : IntermediateField K (LaurentSeries K)) (jres jNres : E)
    (hj : (jres : LaurentSeries K) = jqModC K) (hjN : (jNres : LaurentSeries K) = qExpand K N (jqModC K)) :
    LinearIndependent (IntermediateField.adjoin K ({jNres} : Set E)) (fun i : Fin N => jres ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i

  let preIF : IntermediateField K E :=
    { toSubalgebra := (qExpandAlgHomC K N).fieldRange.toSubalgebra.comap E.val
      inv_mem' := fun x hx => by
        have hx' : E.val x ∈ (qExpandAlgHomC K N).fieldRange := hx
        have h : E.val x⁻¹ ∈ (qExpandAlgHomC K N).fieldRange := by
          rw [map_inv₀]; exact IntermediateField.inv_mem _ hx'
        exact h }
  have mem_preIF : ∀ {x : E}, x ∈ preIF ↔ ((x : E) : LaurentSeries K) ∈ (qExpandAlgHomC K N).fieldRange :=
    Iff.rfl
  have hS : ∀ i, (((g i : E) : LaurentSeries K)) ∈ Set.range (qExpand K N) := by
    intro i
    have hle : IntermediateField.adjoin K ({jNres} : Set E) ≤ preIF := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      show jNres ∈ preIF
      rw [mem_preIF, hjN]
      exact ⟨jqModC K, rfl⟩
    obtain ⟨y, hy⟩ := mem_preIF.mp (hle (g i).2)
    exact ⟨y, hy⟩
  have hrel : ∑ i, ((g i : E) : LaurentSeries K) * jqModC K ^ (i : ℕ) = 0 := by
    have h1 := congrArg E.val hg
    rw [map_sum, map_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.smul_def, smul_eq_mul, map_mul, map_pow, ← hj]
    rfl
  have h0 := eq_zero_of_sum_mul_pow_jqModC_eq_zero K N _ hS hrel i
  exact Subtype.ext (Subtype.ext h0)

theorem transcendental_of_coe (E : IntermediateField K (LaurentSeries K)) {x : E}
    (hx : Transcendental K ((x : E) : LaurentSeries K)) : Transcendental K x :=
  fun h => hx (h.algHom E.val)

theorem transcendental_qExpand_jqModC : Transcendental K (qExpand K N (jqModC K)) := fun h =>
  ModularCurve.transcendental_jqModC K
    ((isAlgebraic_algHom_iff (qExpandAlgHomC K N) (qExpand_injective (R := K) (N := N))).mp h)

end Orders

section Count

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb0" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1

theorem coe_jFun : ((jFun (q := q) : FF) : LaurentSeries QQ) = jqModC QQ := coeffMap_jqModC _

theorem finrank_adjoin_jFun :
    Module.finrank (IntermediateField.adjoin QQ {(jFun (q := q) : FF)}) FF = q + 1 := by
  have hN : (((1 * q : ℕ)) : QQ) ≠ 0 := by exact_mod_cast (mul_ne_zero one_ne_zero (Fact.out : q.Prime).ne_zero)
  have hmem : jqModC QQ ∈ laurentBaseChange QQ (modularFunctionFieldFull (1 * q)) := by
    rw [laurentBaseChange_eq_fullC]; exact jqModC_mem_full QQ (1 * q)
  have hj : (jFun (q := q) : FF) = ⟨jqModC QQ, hmem⟩ := Subtype.ext (coe_jFun (q := q))
  rw [hj]
  show Module.finrank (IntermediateField.adjoin QQ
      ({(⟨jqModC QQ, hmem⟩ : laurentBaseChange QQ (modularFunctionFieldFull (1 * q)))} :
        Set (laurentBaseChange QQ (modularFunctionFieldFull (1 * q)))))
      (laurentBaseChange QQ (modularFunctionFieldFull (1 * q))) = q + 1
  rw [finrank_adjoin_transport QQ (laurentBaseChange_eq_fullC QQ (1 * q)) hmem (jqModC_mem_full QQ (1 * q)),
    ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi QQ (1 * q) hN]
  have h1q : (1 * q : ℕ) = q := one_mul q
  simp only [h1q]
  exact dedekindPsi_prime Fact.out

theorem charP_residueField (hA : A.LiesOverPrime q) : CharP kk q := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hA
  have h0 : (q : kk) = 0 := by
    have hNA : (⟨(q : QQ), hmem⟩ : A) = (q : A) := Subtype.ext (map_natCast A.subtype q).symm
    rw [← map_natCast (IsLocalRing.residue A) q, ← hNA, IsLocalRing.residue_eq_zero_iff]
    exact hmax
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

set_option maxHeartbeats 6400000 in

theorem integers_eq_or_eq_of_transcendental (hA : A.LiesOverPrime q) (V : P.LevelOneProlongationPair)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A FF Fbar)
    (hj : PlaceSpecialization.jFun (q := q) ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨_, hj⟩)) :
    R.integers = V.R₁.integers ∨ R.integers = V.R₂.integers := by
  haveI : CharP kk q := charP_residueField hA
  by_contra hnot
  push_neg at hnot
  obtain ⟨h1, h2⟩ := hnot
  have hne : V.R₁.integers ≠ V.R₂.integers :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_ne_integers hA V
  obtain ⟨hj₁, -, -, hj₂, e₁, -, -, e₂⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun hA V

  let Fb3 : Option Bool → Type := fun o => Option.casesOn o Fbar fun _ => ↥Fb0
  letI instF : ∀ o, Field (Fb3 o) := fun o =>
    match o with
    | none => (inferInstance : Field Fbar)
    | some _ => (inferInstance : Field Fb0)
  letI instA : ∀ o, @Algebra kk (Fb3 o) _ (instF o).toSemifield.toDivisionSemiring.toSemiring :=
    fun o =>
    match o with
    | none => (inferInstance : Algebra kk Fbar)
    | some _ => (inferInstance : Algebra kk Fb0)
  let R3 : ∀ o, @RegularProlongation QQ _ A FF _ _ (Fb3 o) (instF o) (instA o) := fun o =>
    match o with
    | none => R
    | some true => V.R₁
    | some false => V.R₂
  let I3 : Option Bool → ValuationSubring FF := fun o =>
    @RegularProlongation.integers QQ _ A FF _ _ (Fb3 o) (instF o) (instA o) (R3 o)
  have hI3n : I3 none = R.integers := rfl
  have hI3t : I3 (some true) = V.R₁.integers := rfl
  have hI3f : I3 (some false) = V.R₂.integers := rfl

  haveI : FiniteDimensional (IntermediateField.adjoin QQ ({(jFun (q := q) : FF)} : Set FF)) FF :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_jFun]; exact Nat.succ_pos q)

  have hinj : Function.Injective I3 := by
    intro o o' h
    rcases o with _ | b <;> rcases o' with _ | b'
    · rfl
    · cases b'
      · rw [hI3n, hI3f] at h; exact absurd h h2
      · rw [hI3n, hI3t] at h; exact absurd h h1
    · cases b
      · rw [hI3f, hI3n] at h; exact absurd h.symm h2
      · rw [hI3t, hI3n] at h; exact absurd h.symm h1
    · cases b <;> cases b'
      · rfl
      · rw [hI3f, hI3t] at h; exact absurd h.symm hne
      · rw [hI3t, hI3f] at h; exact absurd h hne
      · rfl

  have hf : ∀ o, (jFun (q := q) : FF) ∈ I3 o := fun o =>
    match o with
    | none => hj
    | some true => hj₁
    | some false => hj₂
  obtain ⟨hfin, hsum⟩ :=
    @AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le QQ _ A FF _ _ (Option Bool) _
      Fb3 instF instA R3 hinj (jFun (q := q) : FF) hf (by
        intro o
        match o with
        | none => exact htr
        | some true =>
            refine transcendental_of_coe kk (modularFunctionFieldFullC kk 1) ?_
            show Transcendental kk (((V.R₁.residue ⟨jFun, hj₁⟩ : Fb0)) : LaurentSeries kk)
            rw [e₁]
            exact ModularCurve.transcendental_jqModC kk
        | some false =>
            refine transcendental_of_coe kk (modularFunctionFieldFullC kk 1) ?_
            show Transcendental kk (((V.R₂.residue ⟨jFun, hj₂⟩ : Fb0)) : LaurentSeries kk)
            rw [e₂, ← qExpand_jqModC_eq_pow_unconditional kk]
            exact transcendental_qExpand_jqModC kk q) inferInstance
  rw [Fintype.sum_option, Fintype.sum_bool, finrank_adjoin_jFun] at hsum

  have hpos : ∀ {K V : Type} [Field K] [Field V] [Algebra K V], FiniteDimensional K V →
      0 < Module.finrank K V := fun h => Module.finrank_pos
  have ha := hpos (hfin none)
  have hb := hpos (hfin (some true))
  haveI := hfin (some false)
  have hjc : (((V.R₁.residue ⟨jFun, hj₁⟩ : Fb0)) : LaurentSeries kk) = jqModC kk := e₁
  have hjNc : (((V.R₂.residue ⟨jFun, hj₂⟩ : Fb0)) : LaurentSeries kk) = qExpand kk q (jqModC kk) := by
    rw [e₂, qExpand_jqModC_eq_pow_unconditional kk]
  have hli := (linearIndependent_pow kk q (modularFunctionFieldFullC kk 1) _ _ hjc hjNc).fintype_card_le_finrank
  rw [Fintype.card_fin] at hli
  have hc : q ≤ Module.finrank
      (IntermediateField.adjoin kk ({(R3 (some false)).residue ⟨jFun, hf (some false)⟩} :
        Set (Fb3 (some false)))) (Fb3 (some false)) := hli
  omega

end Count

end Ws25.E2

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (V : P.LevelOneProlongationPair)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A (modularFunctionFieldBar (1 * q)) Fbar)
    (hj : PlaceSpecialization.jFun (q := q) ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨_, hj⟩)) :
    R.integers = V.R₁.integers ∨ R.integers = V.R₂.integers :=
  Ws25.E2.integers_eq_or_eq_of_transcendental hA V R hj htr

end
end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_transcendental
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_transcendental (solution)
