-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.le_ord_residue_and_exists_hasValue_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f5f236ac-837b-5b9b-8f58-f26592f81109

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_ord_residue_and_exists_hasValue_of_mul
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace FltWs29
namespace N3N

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem hasValue_of_mul {K F : Type*} [Field K] [Field F] [Algebra K F]
    {v : Place K F} {x u : F} {c₀ l : K}
    (hu : v.HasValue u l) (hl : l ≠ 0) (hxu : v.HasValue (x * u) c₀) : v.HasValue x (c₀ * l⁻¹) := by
  have hu0 : u ≠ 0 := hu.ne_zero hl
  have : x = (x * u) * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  rw [this]
  exact hxu.mul (hu.inv hl)

theorem main
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (Wset : Finset (Place k ↥(modularFunctionFieldC k N))) (hRL : R.RegularityLaw Wset)
    (w : Place k ↥(modularFunctionFieldC k N)) (hwW : w ∈ Wset)
    (f t : ↥(modularFunctionFieldBar (N * q)))
    (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → 0 ≤ V.ord (f * t))
    (n₁ n₂ : ℤ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (πw : ↥(modularFunctionFieldC k N)) (hπ : w.ord πw = 1)
    (htw₁ : w.HasValue (πw ^ (-n₁) * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • πw) ^ (-n₂) * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    (R.residue₁ ⟨f, hf₁⟩ ≠ 0 → -n₁ ≤ w.ord (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) ∧
    (R.residue₂ ⟨f, hf₂⟩ ≠ 0 → -n₂ ≤ (arithFrobC q k N • w).ord (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) ∧
    ∃ c : k,
      w.HasValue (πw ^ n₁ * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) (l₂ * c) ∧
      (arithFrobC q k N • w).HasValue
        ((arithFrobC q k N • πw) ^ n₂ * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) (l₁ * c) := by

  have hs : (w, arithFrobC q k N • w) ∈ nodePairsOfPlaces (arithFrobC q k N) Wset :=
    smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k N) hwW
  obtain ⟨c₀, hv₁, hv₂⟩ := hRL.2 (f * t) (mul_mem hf₁ ht₁) (mul_mem hf₂ ht₂)
    (w, arithFrobC q k N • w) hs hpole

  have hv₁' : w.HasValue (R.residue₁ ⟨f, hf₁⟩ * R.residue₁ ⟨t, ht₁⟩) c₀ := by
    rw [← map_mul]; exact hv₁
  have hv₂' : (arithFrobC q k N • w).HasValue (R.residue₂ ⟨f, hf₂⟩ * R.residue₂ ⟨t, ht₂⟩) c₀ := by
    rw [← map_mul]; exact hv₂
  clear hv₁ hv₂

  have hoJ₂ : (arithFrobC q k N • w).ord (arithFrobC q k N • πw) = 1 := by
    rw [SemilinearAut.ord_smul]; exact hπ
  have hJ₁0 : πw ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  have hJ₂0 : arithFrobC q k N • πw ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hoJ₂; exact zero_ne_one hoJ₂
  set J₁ : ↥(modularFunctionFieldC k N) := πw with hJ₁
  set J₂ : ↥(modularFunctionFieldC k N) := arithFrobC q k N • πw with hJ₂
  set r₁f : ↥(modularFunctionFieldC k N) := R.residue₁ ⟨f, hf₁⟩ with hr₁f
  set r₁t : ↥(modularFunctionFieldC k N) := R.residue₁ ⟨t, ht₁⟩ with hr₁t
  set r₂f : ↥(modularFunctionFieldC k N) := R.residue₂ ⟨f, hf₂⟩ with hr₂f
  set r₂t : ↥(modularFunctionFieldC k N) := R.residue₂ ⟨t, ht₂⟩ with hr₂t

  have hsplit₁ : r₁f * r₁t = (J₁ ^ n₁ * r₁f) * (J₁ ^ (-n₁) * r₁t) := by
    rw [zpow_neg]
    field_simp
  have hsplit₂ : r₂f * r₂t = (J₂ ^ n₂ * r₂f) * (J₂ ^ (-n₂) * r₂t) := by
    rw [zpow_neg]
    field_simp
  rw [hsplit₁] at hv₁'
  rw [hsplit₂] at hv₂'
  have htv₁ := hasValue_of_mul htw₁ hl₁ hv₁'
  have htv₂ := hasValue_of_mul htw₂ hl₂ hv₂'
  refine ⟨fun hne => ?_, fun hne => ?_, ⟨c₀ * l₁⁻¹ * l₂⁻¹, ?_, ?_⟩⟩
  ·
    have h0 := Place.ord_nonneg_of_mem _ htv₁.mem
    rw [Place.ord_mul _ (zpow_ne_zero n₁ hJ₁0) hne, Place.ord_zpow, hπ, mul_one] at h0
    omega
  ·
    have h0 := Place.ord_nonneg_of_mem _ htv₂.mem
    rw [Place.ord_mul _ (zpow_ne_zero n₂ hJ₂0) hne, Place.ord_zpow, hoJ₂, mul_one] at h0
    omega
  · have : l₂ * (c₀ * l₁⁻¹ * l₂⁻¹) = c₀ * l₁⁻¹ := by field_simp
    rw [this]; exact htv₁
  · have : l₁ * (c₀ * l₁⁻¹ * l₂⁻¹) = c₀ * l₂⁻¹ := by field_simp
    rw [this]; exact htv₂

end FltWs29.N3N

open AlgebraicCurve IsLocalRing ModularCurve in
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (Wset : Finset (Place k ↥(modularFunctionFieldC k N))) (hRL : R.RegularityLaw Wset)
    (w : Place k ↥(modularFunctionFieldC k N)) (hwW : w ∈ Wset)
    (f t : ↥(modularFunctionFieldBar (N * q)))
    (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → 0 ≤ V.ord (f * t))
    (n₁ n₂ : ℤ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (πw : ↥(modularFunctionFieldC k N)) (hπ : w.ord πw = 1)
    (htw₁ : w.HasValue (πw ^ (-n₁) * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • πw) ^ (-n₂) * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    (R.residue₁ ⟨f, hf₁⟩ ≠ 0 → -n₁ ≤ w.ord (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) ∧
    (R.residue₂ ⟨f, hf₂⟩ ≠ 0 → -n₂ ≤ (arithFrobC q k N • w).ord (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) ∧
    ∃ c : k,
      w.HasValue (πw ^ n₁ * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) (l₂ * c) ∧
      (arithFrobC q k N • w).HasValue
        ((arithFrobC q k N • πw) ^ n₂ * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) (l₁ * c) :=
  FltWs29.N3N.main R Wset hRL w hwW f t hf₁ hf₂ ht₁ ht₂ hpole n₁ n₂ l₁ l₂ hl₁ hl₂ πw hπ htw₁ htw₂

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_ord_residue_and_exists_hasValue_of_mul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_le_ord_residue_and_exists_hasValue_of_mul (solution)
