-- Prove2me | solution 1 for ModularCurve.heckeBetaRoof_adjoin_range_union_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/824d6c44-93dc-5dd4-97f5-7c6db76a4464

import Mathlib
import Definitions.Def_ModularCurve_HeckeNamedInputs
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem
import Theorems.Thm_ModularCurve_qExpand_jq_mem_adjoin_of_primes_of_ne
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "dvd_of_eq_roof_beta qExpand qExpand_single qExpand_qExpand algebraMap_apply_eq_single jq ModularPolynomialData FunctionFieldGeneration modularFunctionFieldFull jqd_mem_full coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange towerSubstBar coe_towerSubstBar laurentBaseChange_le_of_divisor_generators_mem qExpand_jq_mem_adjoin_of_primes_of_ne coeffMap_qExpand towerSubstBar_isIntegral"
namespace GBB
p2m_open "ModularCurve"

noncomputable def qExpandAlg (L : Type*) [Field L] (n : ℕ) [NeZero n] : LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L n with
    commutes' := fun r => by
      show qExpand L n (algebraMap L (LaurentSeries L) r) = algebraMap L (LaurentSeries L) r
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[scoped simp] theorem qExpandAlg_apply (L : Type*) [Field L] (n : ℕ) [NeZero n] (x : LaurentSeries L) :
    qExpandAlg L n x = qExpand L n x := rfl

theorem qExpand_congr' {R : Type*} [CommRing R] {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (x : LaurentSeries R) :
    qExpand R n x = qExpand R m x := by subst h; rfl

theorem coeffEmb_qExpand'' (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand (algebraMap ℚ L) n x

theorem ringHom_mem_of_mem_adjoin {L : Type*} [Field L] (T : Subfield (LaurentSeries L))
    (g : LaurentSeries ℚ →+* LaurentSeries L)
    (hgc : ∀ c : ℚ, g (algebraMap ℚ (LaurentSeries ℚ) c) ∈ T)
    {S : Set (LaurentSeries ℚ)} (hS : ∀ s ∈ S, g s ∈ T)
    {y : LaurentSeries ℚ} (hy : y ∈ IntermediateField.adjoin ℚ S) : g y ∈ T := by
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap c => exact hgc c
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end ModularCurve.GBB
p2m_reactivate "P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top.ModularCurve P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top.ModularCurve.GBB"
p2m_reactivate "P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top.ModularCurve"

open ModularCurve.GBB in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ)
    [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (hM : M = N * ℓ * ℓ')
    (hgenQ : FunctionFieldGeneration M) (data : ModularPolynomialData ℓ) (data' : ModularPolynomialData ℓ') :
    Algebra.adjoin L
      (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2)
        ∪ Set.range (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1)) = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  obtain ⟨h₂, hh₂⟩ : ∃ h : N * ℓ' * ℓ ∣ M, h = (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2 := ⟨_, rfl⟩
  obtain ⟨h₁, hh₁⟩ : ∃ h : N * ℓ * ℓ' ∣ M, h = (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1 := ⟨_, rfl⟩
  rw [← hh₁, ← hh₂]

  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : IntermediateField L (LaurentSeries L),
      K₂ = IntermediateField.map (qExpandAlg L ℓ) (laurentBaseChange L (modularFunctionFieldFull (N * ℓ'))) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Set (LaurentSeries L),
      S = Set.range (fun y : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) =>
        ((towerSubstBar L (N * ℓ) ℓ' h₁ y : laurentBaseChange L (modularFunctionFieldFull M)) : LaurentSeries L)) := ⟨_, rfl⟩
  have hmemC : ∀ (P d : ℕ) [NeZero P] [NeZero d], d ∣ P →
      coeffEmb L (qExpand ℚ d jq) ∈ laurentBaseChange L (modularFunctionFieldFull P) :=
    fun P d _ _ hd => coeffEmb_mem_laurentBaseChange L (jqd_mem_full P hd)
  have hK₂mem : ∀ x : laurentBaseChange L (modularFunctionFieldFull (N * ℓ')), qExpand L ℓ (x : LaurentSeries L) ∈ K₂ :=
    fun x => by rw [hK₂, IntermediateField.mem_map]; exact ⟨x, x.2, rfl⟩
  have hK₂ex : ∀ x ∈ K₂, ∃ y ∈ laurentBaseChange L (modularFunctionFieldFull (N * ℓ')), qExpand L ℓ y = x :=
    fun x hx => by rw [hK₂, IntermediateField.mem_map] at hx; exact hx

  have memK₂ : ∀ (e : ℕ) [NeZero e], e ∣ N * ℓ' → coeffEmb L (qExpand ℚ (ℓ * e) jq) ∈ K₂ := by
    intro e _ he
    rw [← qExpand_qExpand, coeffEmb_qExpand'']
    exact hK₂mem ⟨_, hmemC _ _ he⟩

  have memS : ∀ (e : ℕ) [NeZero e], e ∣ N * ℓ → coeffEmb L (qExpand ℚ (ℓ' * e) jq) ∈ S := by
    intro e _ he
    rw [hS]
    refine ⟨⟨coeffEmb L (qExpand ℚ e jq), hmemC _ _ he⟩, ?_⟩
    show ((towerSubstBar L (N * ℓ) ℓ' h₁ _ : laurentBaseChange L (modularFunctionFieldFull M)) : LaurentSeries L) = _
    rw [coe_towerSubstBar, ← coeffEmb_qExpand'', qExpand_qExpand]

  have hZle : laurentBaseChange L (modularFunctionFieldFull M) ≤
      IntermediateField.adjoin L ((K₂ : Set (LaurentSeries L)) ∪ S) := by
    refine laurentBaseChange_le_of_divisor_generators_mem L M _ ?_
    intro d hd0 hdM
    haveI := hd0
    by_cases hℓd : ℓ ∣ d
    · obtain ⟨e, rfl⟩ := hℓd
      haveI : NeZero e := ⟨fun h => NeZero.ne (ℓ * e) (by rw [h, mul_zero])⟩
      have he : e ∣ N * ℓ' := by
        have : ℓ * e ∣ ℓ * (N * ℓ') := by rw [show ℓ * (N * ℓ') = M by rw [hM]; ring]; exact hdM
        exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (NeZero.ne ℓ)) this
      exact IntermediateField.subset_adjoin L _ (Set.mem_union_left _ (memK₂ e he))
    by_cases hℓ'd : ℓ' ∣ d
    · obtain ⟨e, rfl⟩ := hℓ'd
      haveI : NeZero e := ⟨fun h => NeZero.ne (ℓ' * e) (by rw [h, mul_zero])⟩
      have he : e ∣ N * ℓ := by
        have : ℓ' * e ∣ ℓ' * (N * ℓ) := by rw [show ℓ' * (N * ℓ) = M by rw [hM]; ring]; exact hdM
        exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (NeZero.ne ℓ')) this
      exact IntermediateField.subset_adjoin L _ (Set.mem_union_right _ (memS e he))

    have hdN : d ∣ N := by
      have hcop : Nat.Coprime d ℓ := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓd)
      have hcop' : Nat.Coprime d ℓ' := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ').2 hℓ'd)
      have h1 : d ∣ N * ℓ := hcop'.dvd_of_dvd_mul_right (by rw [← hM]; exact hdM)
      exact hcop.dvd_of_dvd_mul_right h1
    have hkey := qExpand_jq_mem_adjoin_of_primes_of_ne d ℓ ℓ' hℓ hℓ' hne
    refine ModularCurve.GBB.ringHom_mem_of_mem_adjoin
      (IntermediateField.adjoin L ((K₂ : Set (LaurentSeries L)) ∪ S)).toSubfield (coeffEmb L) ?_ ?_ hkey
    · intro c
      have : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
        rw [coeffEmb, algebraMap_apply_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]
      rw [this]
      exact (IntermediateField.adjoin L _).algebraMap_mem _
    · rintro s (rfl | rfl | rfl)
      · rw [qExpand_congr' (mul_comm d ℓ)]
        exact IntermediateField.subset_adjoin L _ (Set.mem_union_left _ (memK₂ d (Dvd.dvd.mul_right hdN ℓ')))
      · rw [qExpand_congr' (mul_comm d ℓ')]
        exact IntermediateField.subset_adjoin L _ (Set.mem_union_right _ (memS d (Dvd.dvd.mul_right hdN ℓ)))
      · rw [qExpand_congr' (show d * ℓ * ℓ' = ℓ * (d * ℓ') by ring)]
        exact IntermediateField.subset_adjoin L _ (Set.mem_union_left _ (memK₂ (d * ℓ') (Nat.mul_dvd_mul_right hdN ℓ')))

  have hK₂Z : K₂ ≤ laurentBaseChange L (modularFunctionFieldFull M) := by
    intro x hx
    rw [hK₂, IntermediateField.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (towerSubstBar L (N * ℓ') ℓ h₂ ⟨y, hy⟩).2
  have hSZ : S ⊆ laurentBaseChange L (modularFunctionFieldFull M) := by
    rintro _ hx
    rw [hS] at hx
    obtain ⟨y, rfl⟩ := hx
    exact (towerSubstBar L (N * ℓ) ℓ' h₁ y).2

  have hφ : ∃ φ : laurentBaseChange L (modularFunctionFieldFull (N * ℓ')) →+* K₂,
      ∀ x, ((φ x : K₂) : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
    ⟨((qExpand L ℓ).comp (algebraMap (laurentBaseChange L (modularFunctionFieldFull (N * ℓ'))) (LaurentSeries L))).codRestrict
        K₂ hK₂mem, fun x => rfl⟩
  obtain ⟨φ, hφ⟩ := hφ
  have halgZ : ∀ z : laurentBaseChange L (modularFunctionFieldFull M), IsAlgebraic K₂ (z : LaurentSeries L) := by
    intro z
    obtain ⟨p, hpm, hp0⟩ := towerSubstBar_isIntegral L ℓ h₂ z
    refine IsIntegral.isAlgebraic ⟨p.map φ, hpm.map φ, ?_⟩
    have hcomp : (algebraMap K₂ (LaurentSeries L)).comp φ =
        (algebraMap (laurentBaseChange L (modularFunctionFieldFull M)) (LaurentSeries L)).comp
          (towerSubstBar L (N * ℓ') ℓ h₂).toRingHom :=
      RingHom.ext fun x => hφ x
    have key := Polynomial.hom_eval₂ p (towerSubstBar L (N * ℓ') ℓ h₂).toRingHom
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull M)) (LaurentSeries L)) z
    rw [hp0, map_zero] at key
    rw [Polynomial.eval₂_map, hcomp]
    exact key.symm
  have halgS : ∀ s ∈ S, IsAlgebraic K₂ s := fun s hs => by
    obtain ⟨z, hz, rfl⟩ : ∃ z : laurentBaseChange L (modularFunctionFieldFull M), z = ⟨s, hSZ hs⟩ ∧ (z : LaurentSeries L) = s :=
      ⟨⟨s, hSZ hs⟩, rfl, rfl⟩
    exact halgZ _
  have hring : (IntermediateField.adjoin K₂ S).toSubalgebra = Algebra.adjoin K₂ S :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halgS
  have hres : (IntermediateField.adjoin K₂ S).restrictScalars L =
      IntermediateField.adjoin L ((K₂ : Set (LaurentSeries L)) ∪ S) :=
    IntermediateField.restrictScalars_adjoin (F := L) (K := K₂) (S := S)

  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K₂ (LaurentSeries L), (B : Set (LaurentSeries L)) =
      Subalgebra.map (laurentBaseChange L (modularFunctionFieldFull M)).val
        (Algebra.adjoin L (Set.range (towerSubstBar L (N * ℓ') ℓ h₂) ∪ Set.range (towerSubstBar L (N * ℓ) ℓ' h₁))) := by
    refine ⟨{ (Subalgebra.map (laurentBaseChange L (modularFunctionFieldFull M)).val
        (Algebra.adjoin L (Set.range (towerSubstBar L (N * ℓ') ℓ h₂)
          ∪ Set.range (towerSubstBar L (N * ℓ) ℓ' h₁)))).toSubsemiring with
      algebraMap_mem' := ?_ }, rfl⟩
    intro r
    obtain ⟨y, hy, hyr⟩ := hK₂ex _ r.2
    show algebraMap K₂ (LaurentSeries L) r ∈ Subalgebra.map (laurentBaseChange L (modularFunctionFieldFull M)).val
        (Algebra.adjoin L (Set.range (towerSubstBar L (N * ℓ') ℓ h₂) ∪ Set.range (towerSubstBar L (N * ℓ) ℓ' h₁)))
    rw [IntermediateField.algebraMap_apply, Subalgebra.mem_map]
    refine ⟨towerSubstBar L (N * ℓ') ℓ h₂ ⟨y, hy⟩, Algebra.subset_adjoin (Set.mem_union_left _ ⟨⟨y, hy⟩, rfl⟩), ?_⟩
    rw [IntermediateField.coe_val, coe_towerSubstBar]
    exact hyr
  have hSB : S ⊆ (B : Set (LaurentSeries L)) := by
    intro s hs
    rw [hS] at hs
    obtain ⟨y, rfl⟩ := hs
    rw [hB]
    exact Subalgebra.mem_map.mpr ⟨towerSubstBar L (N * ℓ) ℓ' h₁ y,
      Algebra.subset_adjoin (Set.mem_union_right _ ⟨y, rfl⟩), by rw [IntermediateField.coe_val]⟩
  have hadjB : Algebra.adjoin K₂ S ≤ B := Algebra.adjoin_le hSB

  rw [eq_top_iff]
  rintro z -
  have hz1 : (z : LaurentSeries L) ∈ (IntermediateField.adjoin K₂ S).restrictScalars L := by
    rw [hres]
    exact hZle z.2
  have hz2 : (z : LaurentSeries L) ∈ Algebra.adjoin K₂ S := by
    rw [← hring]
    exact hz1
  have hz3 : (z : LaurentSeries L) ∈ (B : Set (LaurentSeries L)) := hadjB hz2
  rw [hB] at hz3
  obtain ⟨a, ha, haz⟩ := Subalgebra.mem_map.mp hz3
  rw [IntermediateField.coe_val] at haz
  rw [← Subtype.ext haz]
  exact ha

end S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top
end P2MW
export P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top (solution)
