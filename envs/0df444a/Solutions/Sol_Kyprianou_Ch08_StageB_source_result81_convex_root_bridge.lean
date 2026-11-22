-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_convex_root_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T10:43:10.082631+00:00
-- url     : https://prove2.me/submissions/e12bae24-523d-41f5-9ce5-75f70c136157

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem largest_root_of_convex
    (ψ : ℝ → ℝ) (h0 : ψ 0 = 0) (hc : ConvexOn ℝ (Ici (0 : ℝ)) ψ)
    (hcont : ContinuousOn ψ (Ioi (0 : ℝ))) (hlarge : ∀ q : ℝ, ∃ b : ℝ, 0 < b ∧ q < ψ b)
    (q : ℝ) (hq : 0 ≤ q) : IsScaleTransformDomainBridge ψ q := by
  have hseg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) : ψ x ≤ (x / y) * ψ y := by
    have h := hc.2 (x := 0) (y := y) (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      (show y ∈ Ici 0 from hy.le) (sub_nonneg.mpr ((div_le_one hy).mpr hxy))
      (div_nonneg hx hy.le) (by ring : 1 - x/y + x/y = 1)
    simpa only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hy.ne', h0] using h
  obtain ⟨b, hb, hqb⟩ := hlarge q
  have hbeyond (y : ℝ) (hy : b ≤ y) : q < ψ y := by
    by_contra! h
    have hypos := hb.trans_le hy
    have hstep := mul_le_mul_of_nonneg_left h (div_nonneg hb.le hypos.le)
    exact hqb.not_ge ((hseg b y hb.le hy hypos).trans
      (hstep.trans (mul_le_of_le_one_left hq ((div_le_one hypos).mpr hy))))
  have hinter (x : ℝ) (hx : 0 < x) (hxq : ψ x ≤ q) :
      ∃ y : ℝ, x ≤ y ∧ ψ y = q := by
    have hxb : x < b := lt_of_not_ge fun h => (hbeyond x h).not_ge hxq
    obtain ⟨y, hy, hval⟩ :=
      intermediate_value_Icc hxb.le (hcont.mono fun z hz => hx.trans_le hz.1)
        (show q ∈ Icc (ψ x) (ψ b) from ⟨hxq, hqb.le⟩)
    exact ⟨y, hy.1, hval⟩
  have hRbdd : BddAbove (RightRootSet ψ q) := by
    refine ⟨b, fun y hy => ?_⟩
    have hy' : 0 ≤ y ∧ ψ y = q := hy
    exact (lt_of_not_ge fun h => (hbeyond y h).not_ge hy'.2.le).le
  have hRmax : ∃ r, IsGreatest (RightRootSet ψ q) r := by
    by_cases hsome : ∃ a : ℝ, 0 < a ∧ ψ a = q
    · obtain ⟨a, ha, haq⟩ := hsome
      let S := Ici a ∩ ψ ⁻¹' ({q} : Set ℝ)
      have hca : ContinuousOn ψ (Ici a) := hcont.mono (fun _ hx => ha.trans_le hx)
      have hSc : IsClosed S := hca.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
      have hSa : a ∈ S := ⟨Set.mem_Ici.mpr (le_refl a), haq⟩
      have hsub : S ⊆ RightRootSet ψ q := fun _ hx => ⟨ha.le.trans hx.1, hx.2⟩
      have hSbdd : BddAbove S := by
        obtain ⟨B, hB⟩ := hRbdd
        exact ⟨B, fun _ hx => hB (hsub hx)⟩
      have hSr := hSc.csSup_mem ⟨a, hSa⟩ hSbdd
      refine ⟨sSup S, hsub hSr, ?_⟩
      intro x hx
      by_cases hxa : a ≤ x
      · exact le_csSup hSbdd ⟨hxa, (show 0 ≤ x ∧ ψ x = q from hx).2⟩
      · exact (le_of_not_ge hxa).trans (le_csSup hSbdd hSa)
    · have hq0 : q = 0 := by
        by_contra hqne
        have hqp := lt_of_le_of_ne hq (Ne.symm hqne)
        have hpb : 0 < ψ b := hqp.trans hqb
        let a := (q / ψ b) * b
        have ha : 0 < a := mul_pos (div_pos hqp hpb) hb
        have hab : a ≤ b := mul_le_of_le_one_left hb.le ((div_le_one hpb).mpr hqb.le)
        have haEq : (a / b) * ψ b = q := by
          dsimp [a]
          field_simp
        have haq : ψ a ≤ q := (hseg a b ha.le hab hb).trans_eq haEq
        obtain ⟨z, hz, hzq⟩ := hinter a ha haq
        exact hsome ⟨z, ha.trans_le hz, hzq⟩
      refine ⟨0, ⟨le_rfl, h0.trans hq0.symm⟩, fun x hx => ?_⟩
      exact le_of_not_gt fun hp => hsome ⟨x, hp, (show 0 ≤ x ∧ ψ x = q from hx).2⟩
  obtain ⟨r, hr, hrMax⟩ := hRmax
  have hr0 : 0 ≤ r := (show 0 ≤ r ∧ ψ r = q from hr).1
  have hrq : ψ r = q := (show 0 ≤ r ∧ ψ r = q from hr).2
  have hPhi : Phi ψ q = r :=
    le_antisymm (csSup_le ⟨r, hr⟩ (fun _ hx => hrMax hx)) (le_csSup hRbdd hr)
  refine ⟨⟨hq, ?_, ?_⟩, ?_⟩
  · simpa only [hPhi] using hr
  · intro x hx
    rw [hPhi]
    exact hrMax hx
  · intro x hx
    rw [hPhi]
    constructor
    · intro hxr
      by_contra! hxq
      obtain ⟨y, hy, hyq⟩ := hinter x (hr0.trans_lt hxr) hxq
      exact (hrMax ⟨hx.trans hy, hyq⟩).not_gt (hxr.trans_le hy)
    · intro hxq
      by_contra! hxr
      have hxp : 0 < x := by
        by_contra! hn
        have he : x = 0 := le_antisymm hn hx
        exact hxq.not_ge (by simpa only [he, h0] using hq)
      have hrp := hxp.trans_le hxr
      have hscale : x / r ≤ 1 := (div_le_one hrp).mpr hxr
      exact hxq.not_ge ((hseg x r hx hxr hrp).trans
        (by rw [hrq]; exact mul_le_of_le_one_left hq hscale))

theorem solution
    (ψ : ℝ → ℝ) (h0 : ψ 0 = 0) (hc : ConvexOn ℝ (Ici (0 : ℝ)) ψ)
    (hcont : ContinuousOn ψ (Ioi (0 : ℝ))) (hlarge : ∀ q : ℝ, ∃ b : ℝ, 0 < b ∧ q < ψ b)
    (q : ℝ) (hq : 0 ≤ q) : IsScaleTransformDomainBridge ψ q := by
  exact largest_root_of_convex ψ h0 hc hcont hlarge q hq
