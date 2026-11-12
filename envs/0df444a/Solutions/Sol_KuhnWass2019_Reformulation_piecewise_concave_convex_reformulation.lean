-- Prove2me | solution 1 for KuhnWass2019.Reformulation.piecewise_concave_convex_reformulation
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:11:08.327277+00:00
-- url     : https://prove2.me/submissions/8d139837-070c-4939-8be3-9fd31ece1540

import Mathlib
import Definitions.Def_KuhnWass2019_Reformulation_RegularLoss
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_KuhnWass2019_Reformulation_worstCaseRisk
import Definitions.Def_KuhnWass2019_Reformulation_finiteProgramValue
import Definitions.Def_KuhnWass2019_Reformulation_infinityWorstCaseRisk
import Definitions.Def_KuhnWass2019_Reformulation_infinityProgramValue

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

private def ceXi : Set (ℝ × ℝ) := {z | z.2 ≤ 0}

private def ceC : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ 1 ≤ z.1 * z.2}

private def ceSample : Fin 1 → ℝ × ℝ := fun _ => 0

private noncomputable def cePieces : Fin 2 → (ℝ × ℝ) → EReal :=
  fun j z => if j = 0 then 0 else if z ∈ ceC then (z.1 : EReal) else ⊥

private lemma ceXi_convex : Convex ℝ ceXi := by
  intro x hx y hy a b ha hb _
  change x.2 ≤ 0 at hx
  change y.2 ≤ 0 at hy
  change (a • x + b • y).2 ≤ 0
  simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
  nlinarith

private lemma ceXi_closed : IsClosed ceXi :=
  isClosed_le continuous_snd continuous_const

private lemma ceC_closed : IsClosed ceC :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.mul continuous_snd)))

private lemma cePieces_properClosedConvex :
    ∀ j, ShortestGCS.MICP.IsProperClosedConvex (fun x => -cePieces j x) := by
  intro j
  fin_cases j
  · change ShortestGCS.MICP.IsProperClosedConvex (fun x => -cePieces 0 x)
    have hepi0 : ShortestGCS.MICP.epigraph (fun x => -cePieces 0 x) =
        {p : (ℝ × ℝ) × ℝ | 0 ≤ p.2} := by
      ext p
      simp [ShortestGCS.MICP.epigraph, cePieces]
    refine ⟨?_, ?_, ⟨0, by simp [cePieces]⟩, fun x => by simp [cePieces]⟩
    · rw [hepi0]
      intro p hp q hq a b ha hb _
      change 0 ≤ p.2 at hp
      change 0 ≤ q.2 at hq
      change 0 ≤ (a • p + b • q).2
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      nlinarith
    · rw [hepi0]
      exact isClosed_le continuous_const continuous_snd
  · change ShortestGCS.MICP.IsProperClosedConvex (fun x => -cePieces 1 x)
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hepi1 : ShortestGCS.MICP.epigraph (fun x => -cePieces 1 x) =
        {p : (ℝ × ℝ) × ℝ | p.1 ∈ ceC ∧ -p.1.1 ≤ p.2} := by
      ext p
      by_cases hpC : p.1 ∈ ceC
      · simp [ShortestGCS.MICP.epigraph, cePieces, h10, hpC, ← EReal.coe_neg, EReal.coe_le_coe_iff]
      · simp [ShortestGCS.MICP.epigraph, cePieces, h10, hpC]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hepi1]
      intro p hp q hq a b ha hb hab
      change p.1 ∈ ceC ∧ -p.1.1 ≤ p.2 at hp
      change q.1 ∈ ceC ∧ -q.1.1 ≤ q.2 at hq
      change (a • p + b • q).1 ∈ ceC ∧ -(a • p + b • q).1.1 ≤ (a • p + b • q).2
      have hx1_pos : 0 < p.1.1 := by nlinarith [hp.1.1, hp.1.2.1, hp.1.2.2]
      have hy1_pos : 0 < q.1.1 := by nlinarith [hq.1.1, hq.1.2.1, hq.1.2.2]
      have hpx : 0 ≤ p.1.1 * p.1.2 - 1 := sub_nonneg.mpr hp.1.2.2
      have hqx : 0 ≤ q.1.1 * q.1.2 - 1 := sub_nonneg.mpr hq.1.2.2
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        nlinarith [hp.1.1, hq.1.1]
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        nlinarith [hp.1.2.1, hq.1.2.1]
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        have hsos : p.1.1 * q.1.1 *
            ((a * p.1.1 + b * q.1.1) * (a * p.1.2 + b * q.1.2) - (a + b) ^ 2) =
            a ^ 2 * q.1.1 * p.1.1 * (p.1.1 * p.1.2 - 1) +
            b ^ 2 * p.1.1 * q.1.1 * (q.1.1 * q.1.2 - 1) +
            a * b * (p.1.1 ^ 2 * (q.1.1 * q.1.2 - 1) +
              q.1.1 ^ 2 * (p.1.1 * p.1.2 - 1) + (p.1.1 - q.1.1) ^ 2) := by ring
        have hrhs : 0 ≤ a ^ 2 * q.1.1 * p.1.1 * (p.1.1 * p.1.2 - 1) +
            b ^ 2 * p.1.1 * q.1.1 * (q.1.1 * q.1.2 - 1) +
            a * b * (p.1.1 ^ 2 * (q.1.1 * q.1.2 - 1) +
              q.1.1 ^ 2 * (p.1.1 * p.1.2 - 1) + (p.1.1 - q.1.1) ^ 2) := by positivity
        rw [← hsos, hab, one_pow] at hrhs
        have hsub : 0 ≤ (a * p.1.1 + b * q.1.1) * (a * p.1.2 + b * q.1.2) - 1 :=
          (mul_nonneg_iff_of_pos_left (mul_pos hx1_pos hy1_pos)).mp hrhs
        linarith
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        nlinarith [hp.2, hq.2]
    · rw [hepi1]
      exact (ceC_closed.preimage continuous_fst).inter
        (isClosed_le (continuous_fst.comp continuous_fst).neg continuous_snd)
    · refine ⟨(1, 1), ?_⟩
      have h11 : ((1 : ℝ), (1 : ℝ)) ∈ ceC := by simp [ceC]
      dsimp only [cePieces]
      rw [if_neg h10, if_pos h11, ← EReal.coe_neg]
      exact EReal.coe_ne_top (-1)
    · intro x
      by_cases hx : x ∈ ceC <;> simp [cePieces, h10, hx, EReal.coe_ne_top]

private lemma maxLoss_cePieces (z : ℝ × ℝ) :
    WassDDRO.Reduction.maxLoss cePieces z = if z ∈ ceC then (z.1 : EReal) else 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  unfold WassDDRO.Reduction.maxLoss
  refine le_antisymm (iSup_le fun j => ?_) ?_
  · fin_cases j
    · by_cases hz : z ∈ ceC
      · simp only [cePieces, ↓reduceIte, hz]
        exact EReal.coe_nonneg.mpr hz.1
      · simp [cePieces, hz]
    · by_cases hz : z ∈ ceC <;> simp [cePieces, h10, hz]
  · by_cases hz : z ∈ ceC
    · simpa [cePieces, h10, hz] using le_iSup (fun j : Fin 2 => cePieces j z) 1
    · simpa [cePieces, hz] using le_iSup (fun j : Fin 2 => cePieces j z) 0

private lemma ceRegularLoss :
    RegularLoss (WassersteinDRO.Duality.empiricalDistribution ceSample)
      (WassDDRO.Reduction.maxLoss cePieces) := by
  have hmax_eq : WassDDRO.Reduction.maxLoss cePieces =
      fun z : ℝ × ℝ => if z ∈ ceC then (z.1 : EReal) else 0 :=
    funext maxLoss_cePieces
  have hmeas : Measurable (WassDDRO.Reduction.maxLoss cePieces) := by
    rw [hmax_eq]
    exact Measurable.ite ceC_closed.measurableSet
      (continuous_coe_real_ereal.measurable.comp measurable_fst) measurable_const
  refine ⟨hmeas, ?_, ?_⟩
  · intro x b hxb
    rw [maxLoss_cePieces] at hxb
    induction b using EReal.rec with
    | bot => exact absurd hxb not_lt_bot
    | top =>
      refine Filter.Eventually.of_forall fun y => ?_
      change WassDDRO.Reduction.maxLoss cePieces y < ⊤
      rw [maxLoss_cePieces]
      split_ifs <;> simp
    | coe r =>
      by_cases hx : x ∈ ceC
      · rw [if_pos hx, EReal.coe_lt_coe_iff] at hxb
        have hr_pos : 0 < r := lt_of_le_of_lt hx.1 hxb
        refine Filter.eventually_of_mem
          ((isOpen_lt continuous_fst continuous_const).mem_nhds hxb) fun y hy => ?_
        change y.1 < r at hy
        rw [maxLoss_cePieces]
        split_ifs
        · exact EReal.coe_lt_coe_iff.mpr hy
        · exact EReal.coe_pos.mpr hr_pos
      · rw [if_neg hx] at hxb
        refine Filter.eventually_of_mem (ceC_closed.isOpen_compl.mem_nhds hx) fun y hy => ?_
        change y ∉ ceC at hy
        rw [maxLoss_cePieces, if_neg hy]
        exact hxb
  · have hP_eq : WassersteinDRO.Duality.empiricalDistribution ceSample = Measure.dirac 0 := by
      unfold WassersteinDRO.Duality.empiricalDistribution
      rw [Fin.sum_univ_one]
      simp [ceSample]
    rw [hP_eq]
    have h0_not_C : (0 : ℝ × ℝ) ∉ ceC := by simp [ceC]
    have hae : (fun x : ℝ × ℝ =>
        (WassDDRO.Reduction.maxLoss cePieces x).toENNReal +
          (-WassDDRO.Reduction.maxLoss cePieces x).toENNReal) =ᵐ[Measure.dirac 0] 0 := by
      have hnull : (Measure.dirac (0 : ℝ × ℝ)) ({0} : Set (ℝ × ℝ))ᶜ = 0 := by simp
      refine Filter.eventually_of_mem (mem_ae_iff.mpr hnull) fun x hx => ?_
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst hx0
      simp [maxLoss_cePieces, h0_not_C]
    rw [lintegral_congr_ae hae]
    simp

private lemma ceWorstCaseRisk_nonpos :
    worstCaseRisk 1 1 ceXi (WassersteinDRO.Duality.empiricalDistribution ceSample)
      (WassDDRO.Reduction.maxLoss cePieces) ≤ 0 := by
  unfold worstCaseRisk
  refine iSup₂_le fun Q hQ => ?_
  have hQsupp : Q ceXiᶜ = 0 := hQ.2.1
  have hae_zero : ∀ᵐ z ∂Q, WassDDRO.Reduction.maxLoss cePieces z = 0 := by
    refine Filter.eventually_of_mem (mem_ae_iff.mpr hQsupp) ?_
    intro z hz
    have hzC : z ∉ ceC := by
      intro hzc
      have hle0 : z.1 * z.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hzc.1 hz
      linarith [hzc.2.2]
    rw [maxLoss_cePieces, if_neg hzC]
  have hpos_zero : ∫⁻ z, (WassDDRO.Reduction.maxLoss cePieces z).toENNReal ∂Q = 0 := by
    have hae1 : (fun z => (WassDDRO.Reduction.maxLoss cePieces z).toENNReal) =ᵐ[Q] 0 :=
      hae_zero.mono fun z hz => by simp [hz]
    simpa using lintegral_congr_ae hae1
  have hneg_zero : ∫⁻ z, (-WassDDRO.Reduction.maxLoss cePieces z).toENNReal ∂Q = 0 := by
    have hae2 : (fun z => (-WassDDRO.Reduction.maxLoss cePieces z).toENNReal) =ᵐ[Q] 0 :=
      hae_zero.mono fun z hz => by simp [hz]
    simpa using lintegral_congr_ae hae2
  unfold DupacovaWets.Consistency.expect
  simp [hpos_zero, hneg_zero]

private lemma one_le_ceFiniteProgramValue :
    (1 : EReal) ≤ finiteProgramValue 1 1 ceXi ceSample cePieces := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  unfold finiteProgramValue
  refine le_iInf fun γ => le_iInf fun s => le_iInf fun u => le_iInf fun v =>
    le_iInf fun hγ => le_iInf fun hfeas => ?_
  rw [Real.one_rpow, mul_one, Nat.cast_one, div_one, one_mul, Fin.sum_univ_one]
  suffices hreal : 1 ≤ γ + s 0 by exact EReal.coe_le_coe_iff.mpr hreal
  have hs0 : 0 ≤ s 0 := by
    have h00 := hfeas 0 0
    have hA1 : (0 : EReal) ≤
        WassDDRO.Reduction.conjOn Set.univ (fun x => -cePieces 0 x) (u 0 0 - v 0 0) := by
      unfold WassDDRO.Reduction.conjOn
      exact le_iSup₂_of_le (0 : ℝ × ℝ) (Set.mem_univ _) (by simp [cePieces])
    have hA2 : (0 : EReal) ≤ WassDDRO.Reduction.supportFun ceXi (v 0 0) := by
      unfold WassDDRO.Reduction.supportFun
      exact le_iSup₂_of_le (0 : ℝ × ℝ) (by simp [ceXi]) (by simp)
    have hA3 : ((u 0 0 (ceSample 0) : ℝ) : EReal) = 0 := by simp [ceSample]
    have hA4 : (0 : EReal) ≤ powerPerspective 1 γ (u 0 0) := by
      unfold powerPerspective
      rw [if_pos rfl]
      split_ifs <;> simp
    have hle : (0 : EReal) ≤ (s 0 : EReal) := by
      rw [hA3, sub_zero] at h00
      exact (add_nonneg (add_nonneg hA1 hA2) hA4).trans h00
    exact EReal.coe_le_coe_iff.mp hle
  have h01 := hfeas 0 1
  have hA3_1 : ((u 0 1 (ceSample 0) : ℝ) : EReal) = 0 := by simp [ceSample]
  rw [hA3_1, sub_zero] at h01
  have hbound_t : ∀ {t : ℝ}, 0 < t →
      (((u 0 1 (t, t⁻¹) - v 0 1 (t, t⁻¹) + t + v 0 1 (t, 0)) : ℝ) : EReal) ≤
        WassDDRO.Reduction.conjOn Set.univ (fun x => -cePieces 1 x) (u 0 1 - v 0 1) +
          WassDDRO.Reduction.supportFun ceXi (v 0 1) := by
    intro t ht
    have htC : (t, t⁻¹) ∈ ceC := by
      refine ⟨ht.le, by positivity, ?_⟩
      rw [mul_inv_cancel₀ ht.ne']
    have h1 : (((u 0 1 (t, t⁻¹) - v 0 1 (t, t⁻¹) + t) : ℝ) : EReal) ≤
        WassDDRO.Reduction.conjOn Set.univ (fun x => -cePieces 1 x) (u 0 1 - v 0 1) := by
      unfold WassDDRO.Reduction.conjOn
      refine le_iSup₂_of_le (t, t⁻¹) (Set.mem_univ _) ?_
      have hc1 : -cePieces 1 (t, t⁻¹) = ((-t : ℝ) : EReal) := by
        simp [cePieces, h10, htC, EReal.coe_neg]
      dsimp only
      rw [hc1]
      simp only [sub_apply]
      rw [← EReal.coe_sub, sub_neg_eq_add]
    have h2 : ((v 0 1 (t, 0) : ℝ) : EReal) ≤ WassDDRO.Reduction.supportFun ceXi (v 0 1) := by
      unfold WassDDRO.Reduction.supportFun
      exact le_iSup₂_of_le (t, 0) (by simp [ceXi]) le_rfl
    rw [EReal.coe_add]
    exact add_le_add h1 h2
  have hu_norm : ‖u 0 1‖ ≤ γ := by
    by_contra hnot
    have hpp : powerPerspective 1 γ (u 0 1) = ⊤ := by
      unfold powerPerspective
      rw [if_neg (not_lt.mpr hγ), if_pos rfl, if_neg hnot]
    have h1 := hbound_t zero_lt_one
    let r₁ : ℝ := u 0 1 (1, 1⁻¹) - v 0 1 (1, 1⁻¹) + 1 + v 0 1 (1, 0)
    have htop : (⊤ : EReal) ≤ (s 0 : EReal) := by
      calc
        (⊤ : EReal) = (r₁ : EReal) + ⊤ := (EReal.coe_add_top r₁).symm
        _ ≤ (WassDDRO.Reduction.conjOn Set.univ (fun x => -cePieces 1 x) (u 0 1 - v 0 1) +
              WassDDRO.Reduction.supportFun ceXi (v 0 1)) + powerPerspective 1 γ (u 0 1) := by
          rw [hpp]
          exact add_le_add h1 le_rfl
        _ ≤ (s 0 : EReal) := h01
    exact EReal.coe_ne_top (s 0) (top_unique htop)
  have hpp0 : powerPerspective 1 γ (u 0 1) = 0 := by
    unfold powerPerspective
    rw [if_neg (not_lt.mpr hγ), if_pos rfl, if_pos hu_norm]
  rw [hpp0, add_zero] at h01
  have hquad : ∀ {t : ℝ}, 0 < t →
      t ^ 2 * (u 0 1 (1, 0) + 1) + (u 0 1 (0, 1) - v 0 1 (0, 1)) ≤ t * s 0 := by
    intro t ht
    have hreal : u 0 1 (t, t⁻¹) - v 0 1 (t, t⁻¹) + t + v 0 1 (t, 0) ≤ s 0 :=
      EReal.coe_le_coe_iff.mp ((hbound_t ht).trans h01)
    have hp1 : (t, t⁻¹) = t • ((1 : ℝ), (0 : ℝ)) + t⁻¹ • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have hp2 : (t, (0 : ℝ)) = t • ((1 : ℝ), (0 : ℝ)) := by
      ext <;> simp
    have hu_eq : u 0 1 (t, t⁻¹) = t * u 0 1 (1, 0) + t⁻¹ * u 0 1 (0, 1) := by
      rw [hp1, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hv_eq : v 0 1 (t, t⁻¹) = t * v 0 1 (1, 0) + t⁻¹ * v 0 1 (0, 1) := by
      rw [hp1, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hv0_eq : v 0 1 (t, 0) = t * v 0 1 (1, 0) := by
      rw [hp2, map_smul, smul_eq_mul]
    rw [hu_eq, hv_eq, hv0_eq] at hreal
    have hmul := mul_le_mul_of_nonneg_left hreal ht.le
    have hident : t * (t * u 0 1 (1, 0) + t⁻¹ * u 0 1 (0, 1) -
        (t * v 0 1 (1, 0) + t⁻¹ * v 0 1 (0, 1)) + t + t * v 0 1 (1, 0)) =
        t ^ 2 * (u 0 1 (1, 0) + 1) + (u 0 1 (0, 1) - v 0 1 (0, 1)) := by
      have ht0 : t ≠ 0 := ht.ne'
      field_simp [ht0]
      ring
    linarith
  have hu10 : u 0 1 (1, 0) ≤ -1 := by
    by_contra hlt
    have hlt' : -1 < u 0 1 (1, 0) := not_le.mp hlt
    let δ : ℝ := u 0 1 (1, 0) + 1
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let B : ℝ := u 0 1 (0, 1) - v 0 1 (0, 1)
    let t : ℝ := max 1 ((|s 0| + |B| + 1) / δ)
    have ht1 : 1 ≤ t := le_max_left _ _
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have htδ : |s 0| + |B| + 1 ≤ t * δ := (div_le_iff₀ hδ).mp (le_max_right _ _)
    have ht2δ : t * (|s 0| + |B| + 1) ≤ t ^ 2 * δ := by
      have h := mul_le_mul_of_nonneg_left htδ ht_pos.le
      have hring : t * (t * δ) = t ^ 2 * δ := by ring
      linarith
    have hts : t * s 0 ≤ t * |s 0| := mul_le_mul_of_nonneg_left (le_abs_self (s 0)) ht_pos.le
    have htB : |B| ≤ t * |B| := by
      simpa using mul_le_mul_of_nonneg_right ht1 (abs_nonneg B)
    have hnegB : -B ≤ |B| := neg_le_abs B
    have hq := hquad ht_pos
    change t ^ 2 * δ + B ≤ t * s 0 at hq
    linarith
  have hnorm10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hop := (u 0 1).le_opNorm ((1 : ℝ), (0 : ℝ))
  rw [hnorm10, mul_one, Real.norm_eq_abs] at hop
  have habs : 1 ≤ |u 0 1 (1, 0)| := by linarith [neg_le_abs (u 0 1 (1, 0))]
  linarith

end KuhnWass2019.Reformulation

open KuhnWass2019.Reformulation in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N J : ℕ} (_hN : 0 < N) (_hJ : 0 < J)
    (Ξ : Set E) (_hΞc : Convex ℝ Ξ) (_hΞcl : IsClosed Ξ)
    (ξhat : Fin N → E) (_hξ : ∀ i, ξhat i ∈ Ξ)
    (ℓ : Fin J → E → EReal) (_hpieces : ∀ j, ShortestGCS.MICP.IsProperClosedConvex (fun x => -ℓ j x))
    (_hℓ : RegularLoss (WassersteinDRO.Duality.empiricalDistribution ξhat)
      (WassDDRO.Reduction.maxLoss ℓ))
    (ε : ℝ) (_hε : 0 ≤ ε),
    (∀ p : ℝ, 1 ≤ p →
      worstCaseRisk ε p Ξ (WassersteinDRO.Duality.empiricalDistribution ξhat)
        (WassDDRO.Reduction.maxLoss ℓ) = finiteProgramValue ε p Ξ ξhat ℓ) ∧
    infinityWorstCaseRisk ε Ξ (WassersteinDRO.Duality.empiricalDistribution ξhat)
      (WassDDRO.Reduction.maxLoss ℓ) = infinityProgramValue ε Ξ ξhat ℓ) := by
  intro hall
  have h := (hall (E := ℝ × ℝ) Nat.one_pos Nat.zero_lt_two
    ceXi ceXi_convex ceXi_closed
    ceSample (fun _ => by simp [ceXi, ceSample])
    cePieces cePieces_properClosedConvex ceRegularLoss
    1 zero_le_one).1 1 le_rfl
  have hle : ((1 : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) :=
    (one_le_ceFiniteProgramValue.trans h.symm.le).trans ceWorstCaseRisk_nonpos
  exact absurd (EReal.coe_le_coe_iff.mp hle) (by norm_num)
