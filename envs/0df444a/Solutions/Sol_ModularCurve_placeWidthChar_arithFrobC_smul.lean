-- Prove2me | solution 1 for ModularCurve.placeWidthChar_arithFrobC_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b313f971-5f70-5838-9d64-afa97d24cbb0

import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeWidthChar_arithFrobC_smul
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_placeWidthChar_arithFrobC_smul.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jWidthChar placeWidthChar placeRamificationJ jGeomGen modularFunctionFieldC jWidth arithFrobC baseAut_arithFrobC_apply arithFrobC_smul_jq"
namespace PlaceWidthCharFrob
p2m_open "ModularCurve"

theorem jWidthChar_pow_char (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] [DecidableEq K] (a : K) :
    jWidthChar q (a ^ q) = jWidthChar q a := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have h0 : a ^ q = 0 ↔ a = 0 := pow_eq_zero_iff hq0
  have h1728 : (1728 : K) ^ q = 1728 := by
    rw [← frobenius_def]; exact map_ofNat (frobenius K q) 1728
  have hjw : jWidth (a ^ q) = jWidth a := by
    by_cases h : a = 0 ∨ a = 1728
    · have ha : a ^ q = a := by
        rcases h with rfl | rfl
        · exact zero_pow hq0
        · exact h1728
      rw [ha]
    · push_neg at h
      have h0' : a ^ q ≠ 0 := pow_ne_zero _ h.1
      have h1' : a ^ q ≠ 1728 := by
        intro e
        apply h.2
        apply frobenius_inj K q
        rw [frobenius_def, frobenius_def, e, h1728]
      simp [jWidth, h.1, h.2, h0', h1']
  unfold jWidthChar
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hq0]
  · have ha' : a ^ q ≠ 0 := fun h => ha (h0.mp h)
    simp only [if_neg ha, if_neg ha', hjw]

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_smul_iff_of_smul_eq (g : SemilinearAut K F) (v : Place K F) {f : F} (hf : g • f = f) :
    f ∈ (g • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  have h := ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := v.toValuationSubring) (x := f)
  rw [hf] at h
  rw [SemilinearAut.smul_toValuationSubring]
  exact h

theorem residue_smul_eq (g : SemilinearAut K F) (v : Place K F) {f : F} (hf : g • f = f)
    (h : f ∈ v.toValuationSubring) (h' : f ∈ (g • v).toValuationSubring) :
    IsLocalRing.residue (g • v).toValuationSubring ⟨f, h'⟩
      = SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨f, h⟩) := by
  have he : SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, h⟩ = ⟨f, h'⟩ :=
    Subtype.ext (by rw [SemilinearAut.coe_smulValuationSubringEquiv_apply]; exact hf)
  rw [← he]
  show _ = IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem ord_sub_algebraMap_eq_zero (v : Place K F) {f : F} (h : f ∈ v.toValuationSubring)
    (hn : ¬ ∃ a : K, algebraMap K v.ResidueField a = IsLocalRing.residue v.toValuationSubring ⟨f, h⟩) (c : K) :
    v.ord (f - algebraMap K F c) = 0 := by
  have hm : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem h (v.algebraMap_mem' c)
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f - algebraMap K F c, hm⟩ ≠ 0 := by
    intro h0
    apply hn
    refine ⟨c, ?_⟩
    have hx : (⟨f - algebraMap K F c, hm⟩ : v.toValuationSubring)
        = ⟨f, h⟩ - algebraMap K v.toValuationSubring c := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
    rw [hx, map_sub, sub_eq_zero] at h0
    rw [h0]
    rfl
  have hunit : IsUnit (⟨f - algebraMap K F c, hm⟩ : v.toValuationSubring) := by
    by_contra hnu
    exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have := v.ord_coe_unit hunit.unit
  rwa [IsUnit.unit_spec] at this

end ModularCurve.PlaceWidthCharFrob

open ModularCurve.PlaceWidthCharFrob in

theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N]
    {K : Type*} [Field K] [CharP K q] [PerfectField K] [DecidableEq K]
    (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N (arithFrobC q K N • w) = placeWidthChar q N w := by
  classical
  set g := arithFrobC q K N with hg
  have hgj : g • jGeomGen K N = jGeomGen K N := arithFrobC_smul_jq q K N
  have hmem := mem_smul_iff_of_smul_eq g w hgj
  have hord : ∀ c : K, (g • w).ord (jGeomGen K N - algebraMap K _ (c ^ q)) = w.ord (jGeomGen K N - algebraMap K _ c) := by
    intro c
    have h1 : g • (jGeomGen K N - algebraMap K _ c) = jGeomGen K N - algebraMap K _ (c ^ q) := by
      rw [smul_sub, hgj, SemilinearAut.smul_algebraMap, hg, baseAut_arithFrobC_apply]
    rw [← h1, SemilinearAut.ord_smul]
  by_cases hA : jGeomGen K N ∈ w.toValuationSubring
  · have hA' : jGeomGen K N ∈ (g • w).toValuationSubring := hmem.mpr hA
    have hres := residue_smul_eq g w hgj hA hA'
    by_cases hrange : ∃ a₀ : K, algebraMap K w.ResidueField a₀ = IsLocalRing.residue w.toValuationSubring ⟨_, hA⟩
    · obtain ⟨a₀, ha₀⟩ := hrange
      have e1 : w.evalAt (jGeomGen K N) = a₀ := by
        rw [w.evalAt_of_mem hA, ← ha₀, Place.residueInv_algebraMap]
      have e2 : (g • w).evalAt (jGeomGen K N) = a₀ ^ q := by
        rw [(g • w).evalAt_of_mem hA', hres, ← ha₀, SemilinearAut.smulResidueRingEquiv_algebraMap, hg,
          baseAut_arithFrobC_apply, Place.residueInv_algebraMap]
      unfold placeWidthChar placeRamificationJ
      rw [e1, e2, jWidthChar_pow_char q a₀, hord a₀]
    · have hrange' : ¬ ∃ b : K, algebraMap K (g • w).ResidueField b
          = IsLocalRing.residue (g • w).toValuationSubring ⟨_, hA'⟩ := by
        rintro ⟨b, hb⟩
        apply hrange
        refine ⟨(SemilinearAut.baseAut g).symm b, ?_⟩
        apply (SemilinearAut.smulResidueRingEquiv g w).injective
        rw [SemilinearAut.smulResidueRingEquiv_algebraMap, RingEquiv.apply_symm_apply, hb, hres]
      have r1 : placeRamificationJ N w = 0 := by
        unfold placeRamificationJ
        rw [ord_sub_algebraMap_eq_zero w hA hrange]; rfl
      have r2 : placeRamificationJ N (g • w) = 0 := by
        unfold placeRamificationJ
        rw [ord_sub_algebraMap_eq_zero (g • w) hA' hrange']; rfl
      unfold placeWidthChar
      rw [r1, r2, Nat.div_zero, Nat.div_zero]
  · have hA' : jGeomGen K N ∉ (g • w).toValuationSubring := fun h => hA (hmem.mp h)
    have e1 : w.evalAt (jGeomGen K N) = 0 := by rw [Place.evalAt, dif_neg hA]
    have e2 : (g • w).evalAt (jGeomGen K N) = 0 := by rw [Place.evalAt, dif_neg hA']
    have h0 : ((0 : K) ^ q) = 0 := zero_pow (Fact.out : q.Prime).ne_zero
    unfold placeWidthChar placeRamificationJ
    rw [e1, e2]
    have := hord 0
    rw [h0] at this
    rw [this]

end S_ModularCurve_placeWidthChar_arithFrobC_smul
end P2MW
export P2MW.S_ModularCurve_placeWidthChar_arithFrobC_smul (solution)
