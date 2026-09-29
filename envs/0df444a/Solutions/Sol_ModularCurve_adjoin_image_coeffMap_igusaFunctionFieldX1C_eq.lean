-- Prove2me | solution 1 for ModularCurve.adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1b3b464f-2ce5-5599-91e4-ee27d6786be2

import Mathlib
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq

set_option autoImplicit false

open ModularCurve

namespace MapIndep

theorem igusaFunctionFieldX1C_eq_igusaFunctionFieldX1C
    (κ : Type*) [Field κ] (M : ℕ) (w w' : IntegralWeightOneForm κ M) :
    igusaFunctionFieldX1C κ M w = igusaFunctionFieldX1C κ M w' := by

  have key : ∀ (u u' : IntegralWeightOneForm κ M), u'.hasseRootFn ∈ igusaFunctionFieldX1C κ M u := by
    intro u u'
    have hr : intSeriesC κ u.series / intSeriesC κ u'.series ∈ x1FunctionFieldC κ M :=
      intFormRatiosC_subset κ _ (mem_intFormRatiosC u.form u'.form u.isIntegralQExp u'.isIntegralQExp u'.intSeriesC_ne_zero)
    have h1 : u'.hasseRootFn = u.hasseRootFn * (intSeriesC κ u.series / intSeriesC κ u'.series) := by
      simp only [IntegralWeightOneForm.hasseRootFn]
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ u.intSeriesC_ne_zero, one_mul]
    rw [h1]
    exact mul_mem (hasseRootFn_mem_igusaFunctionFieldX1C κ M u)
      (x1FunctionFieldC_le_igusaFunctionFieldX1C κ M u hr)
  have hle : ∀ (u u' : IntegralWeightOneForm κ M), igusaFunctionFieldX1C κ M u' ≤ igusaFunctionFieldX1C κ M u := by
    intro u u'
    change IntermediateField.adjoin κ ((x1FunctionFieldC κ M : Set (LaurentSeries κ)) ∪ {u'.hasseRootFn}) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact x1FunctionFieldC_le_igusaFunctionFieldX1C κ M u hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact key u u'
  exact le_antisymm (hle w' w) (hle w w')

end MapIndep

theorem solution
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k] (M : ℕ)
    (w : IntegralWeightOneForm κ M) (w' : IntegralWeightOneForm k M) :
    IntermediateField.adjoin k
        (⇑(coeffMap (algebraMap κ k)) '' (igusaFunctionFieldX1C κ M w : Set (LaurentSeries κ))) =
      igusaFunctionFieldX1C k M w' := by
  classical
  set g : κ →+* k := algebraMap κ k with hg
  set Φ : LaurentSeries κ →+* LaurentSeries k := coeffMap g with hΦ
  have hΦapp : ∀ x : LaurentSeries κ, Φ x = x.map g := fun x => rfl

  have hint : ∀ p : PowerSeries ℤ, Φ (intSeriesC κ p) = intSeriesC k p := by
    intro p
    ext n
    change g ((HahnSeries.ofPowerSeries ℤ κ (p.map (Int.castRingHom κ))).coeff n) =
      (HahnSeries.ofPowerSeries ℤ k (p.map (Int.castRingHom k))).coeff n
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
    · have hr : n ∉ Set.range (fun m : ℕ => (m : ℤ)) := by
        rintro ⟨m, hm⟩
        simp only at hm
        omega
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range hr, HahnSeries.ofPowerSeries_apply,
        HahnSeries.embDomain_notin_range hr, map_zero]

  have hinj : Function.Injective Φ := Φ.injective

  have hrat : ⇑Φ '' intFormRatiosC κ (CongruenceSubgroup.Gamma1 M) = intFormRatiosC k (CongruenceSubgroup.Gamma1 M) := by
    ext x
    constructor
    · rintro ⟨y, ⟨wt, f, f', pf, pg, hf, hg', hg0, rfl⟩, rfl⟩
      refine ⟨wt, f, f', pf, pg, hf, hg', ?_, ?_⟩
      · rw [← hint]; exact fun h0 => hg0 (hinj (by rw [h0, map_zero]))
      · rw [map_div₀, hint, hint]
    · rintro ⟨wt, f, f', pf, pg, hf, hg', hg0, rfl⟩
      refine ⟨intSeriesC κ pf / intSeriesC κ pg, ⟨wt, f, f', pf, pg, hf, hg', ?_, rfl⟩, ?_⟩
      · intro h0; apply hg0; rw [← hint, h0, map_zero]
      · rw [map_div₀, hint, hint]

  have hC : ∀ c : κ, Φ (algebraMap κ (LaurentSeries κ) c) = algebraMap k (LaurentSeries k) (g c) := by
    intro c
    have h1 : algebraMap κ (LaurentSeries κ) c = HahnSeries.C c := by
      first
        | rfl
        | (rw [HahnSeries.algebraMap_apply']; simp)
        | (rw [HahnSeries.algebraMap_apply]; simp)
        | simp
    have h2 : algebraMap k (LaurentSeries k) (g c) = HahnSeries.C (g c) := by
      first
        | rfl
        | (rw [HahnSeries.algebraMap_apply']; simp)
        | (rw [HahnSeries.algebraMap_apply]; simp)
        | simp
    rw [h1, h2, hΦapp, HahnSeries.map_C]

  have hadj : ∀ T : Set (LaurentSeries κ),
      IntermediateField.adjoin k (⇑Φ '' (IntermediateField.adjoin κ T : Set (LaurentSeries κ))) =
        IntermediateField.adjoin k (⇑Φ '' T) := by
    intro T
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ T) := hz
      have hΦz : Φ z ∈ (Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ T)).map Φ := ⟨z, hz', rfl⟩
      rw [RingHom.map_field_closure] at hΦz
      refine (Subfield.closure_le (t := (IntermediateField.adjoin k (⇑Φ '' T)).toSubfield)).mpr ?_ hΦz
      rintro _ ⟨y, hy | hy, rfl⟩
      · obtain ⟨c, rfl⟩ := hy
        rw [hC]
        exact (IntermediateField.adjoin k (⇑Φ '' T)).algebraMap_mem (g c)
      · exact IntermediateField.subset_adjoin k _ ⟨y, hy, rfl⟩
    · exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono (IntermediateField.subset_adjoin κ T))

  have hne : intSeriesC k w.series ≠ 0 := by
    rw [← hint]; exact fun h0 => w.intSeriesC_ne_zero (hinj (by rw [h0, map_zero]))
  let wk : IntegralWeightOneForm k M := ⟨w.form, w.series, w.isIntegralQExp, hne⟩
  have ha : Φ w.hasseRootFn = wk.hasseRootFn := by
    change Φ (intSeriesC κ w.series)⁻¹ = (intSeriesC k w.series)⁻¹
    rw [map_inv₀, hint]
  rw [MapIndep.igusaFunctionFieldX1C_eq_igusaFunctionFieldX1C k M w' wk]
  have hK0 : IntermediateField.adjoin k (⇑Φ '' (x1FunctionFieldC κ M : Set (LaurentSeries κ))) = x1FunctionFieldC k M := by
    change IntermediateField.adjoin k (⇑Φ '' (IntermediateField.adjoin κ (intFormRatiosC κ (CongruenceSubgroup.Gamma1 M)) : Set _)) =
      IntermediateField.adjoin k (intFormRatiosC k (CongruenceSubgroup.Gamma1 M))
    rw [hadj, hrat]
  change IntermediateField.adjoin k (⇑Φ '' (IntermediateField.adjoin κ ((x1FunctionFieldC κ M : Set (LaurentSeries κ)) ∪ {w.hasseRootFn}) : Set _)) =
    IntermediateField.adjoin k ((x1FunctionFieldC k M : Set (LaurentSeries k)) ∪ {wk.hasseRootFn})
  rw [hadj, Set.image_union, Set.image_singleton, ha]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · have hx' : x ∈ x1FunctionFieldC k M := by
        rw [← hK0]; exact IntermediateField.subset_adjoin k _ hx
      exact IntermediateField.subset_adjoin k _ (Or.inl hx')
    · exact IntermediateField.subset_adjoin k _ (Or.inr hx)
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · have hx' : x ∈ IntermediateField.adjoin k (⇑Φ '' (x1FunctionFieldC κ M : Set (LaurentSeries κ))) := by rw [hK0]; exact hx
      exact IntermediateField.adjoin.mono k _ _ Set.subset_union_left hx'
    · exact IntermediateField.subset_adjoin k _ (Or.inr hx)

#print axioms solution

end S_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
end P2MW
export P2MW.S_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq (solution)
