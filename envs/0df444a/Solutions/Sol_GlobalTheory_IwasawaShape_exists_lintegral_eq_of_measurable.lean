-- Prove2me | solution 1 for GlobalTheory.IwasawaShape.exists_lintegral_eq_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:30.659478+00:00
-- url     : https://prove2.me/submissions/6b3d8e98-3160-4bb3-af18-cc4f1fe32492

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable
import Theorems.Thm_GlobalTheory_IwasawaShape_exists_lintegral_eq_mul
import Theorems.Thm_GlobalTheory_IwasawaShape_exists_map_mul_right_eq_smul
import Theorems.Thm_GlobalTheory_IwasawaShape_lintegral_mul_left_of_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.IwasawaShape
theorem _root_.solution (N M K : Subgroup G) (hN : IsClosed (N : Set G))
    (hM : IsClosed (M : Set G)) (hK : IsCompact (K : Set G)) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (huniq : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) (hdec : ∀ g, ∃ u ∈ N, ∃ m ∈ M, ∃ k ∈ K, g = u * m * k)
    (μ μN μM μK : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0)
    [IsFiniteMeasureOnCompacts μN] [IsFiniteMeasureOnCompacts μM] [IsProbabilityMeasure μK]
    (C : Set G) (hC : IsCompact C) (hC0 : μN C ≠ 0) (hM0 : μM ≠ 0)
    (h1 : μN (N : Set G)ᶜ = 0) (h2 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM)
    (iK : ∀ s ∈ K, μK.map (fun g => s * g) = μK) (δ : G → ENNReal) (hδ : Measurable δ)
    (hmod : ∀ m ∈ M, μN.map (fun u => m * u * m⁻¹) = δ m • μN) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  have aN : ∀ᵐ u ∂μN, u ∈ N := mem_ae_iff.2 h1
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h2
  have hC1 : μN C ≠ ⊤ := hC.measure_lt_top.ne
  have hN0 : μN Set.univ ≠ 0 := fun h => hC0 (measure_mono_null (Set.subset_univ _) h)
  have cm : ∀ m : G, Measurable fun u : G => m * u * m⁻¹ := fun m => (measurable_const_mul m).mul_const _
  have hval : ∀ m ∈ M, ∀ S, MeasurableSet S → μN ((fun u => m * u * m⁻¹) ⁻¹' S) = δ m * μN S := by
    intro m hm S hS
    rw [← Measure.map_apply (cm m) hS, hmod m hm]
    simp
  have hmul : ∀ m ∈ M, ∀ m' ∈ M, δ (m * m') = δ m * δ m' := by
    intro m hm m' hm'
    rw [← ENNReal.mul_left_inj hC0 hC1, ← hval _ (M.mul_mem hm hm') C hC.measurableSet, mul_comm (δ m), mul_assoc,
      ← hval m hm C hC.measurableSet, ← hval m' hm' _ (cm m hC.measurableSet)]
    congr 1
    ext u
    simp only [Set.mem_preimage, mul_inv_rev, mul_assoc]
  have hδ0 : ∀ m ∈ M, δ m ≠ 0 := by
    intro m hm h
    have := hval m hm _ MeasurableSet.univ
    rw [h, zero_mul, Set.preimage_univ] at this
    exact hN0 this
  set ρ : Measure G := (μN.prod (μM.withDensity δ)).map (fun z => z.1 * z.2) with hρd
  have hρ : ∀ f : G → ENNReal, Measurable f → ∫⁻ x, f x ∂ρ = ∫⁻ u, ∫⁻ m, δ m * f (u * m) ∂μM ∂μN := by
    intro f hf
    rw [hρd, lintegral_map hf measurable_mul,
      lintegral_prod (fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul).aemeasurable]
    refine lintegral_congr fun u => ?_
    exact lintegral_withDensity_eq_lintegral_mul μM hδ (g := fun m => f (u * m)) (hf.comp (measurable_const_mul u))
  have hF : ∀ f : G → ENNReal, Measurable f → ∀ x : G, Measurable fun u => ∫⁻ m, δ m * f (u * x * m) ∂μM := by
    intro f hf x
    exact Measurable.lintegral_prod_right' (f := fun z : G × G => δ z.2 * f (z.1 * x * z.2))
      ((hδ.comp measurable_snd).mul (hf.comp ((measurable_fst.mul_const x).mul measurable_snd)))
  have lN : ∀ s ∈ N, ρ.map (fun g => s * g) = ρ := by
    intro s hs
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_const_mul s), hρ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
      hρ f hf]
    have := lintegral_mul_left_of_map (iN s hs) _ (hF f hf 1)
    simpa only [mul_one, mul_assoc] using this
  have lM : ∀ s ∈ M, ρ.map (fun g => s * g) = ρ := by
    intro s hs
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_const_mul s), hρ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
      hρ f hf]
    have e := lintegral_map (μ := μN) (hF f hf s) (cm s)
    rw [hmod s hs, lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul _ (hF f hf s)] at e
    calc _ = ∫⁻ u, ∫⁻ m, δ m * f (s * u * s⁻¹ * s * m) ∂μM ∂μN := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = _ := by
          rw [← e]
          refine lintegral_congr fun u => ?_
          rw [← lintegral_mul_left_of_map (iM s hs) (fun m => δ m * f (u * m))
            (hδ.mul (hf.comp (measurable_const_mul u))),
            ← lintegral_const_mul (f := fun m => δ m * f (u * s * m)) _
              (hδ.mul (hf.comp (measurable_const_mul _)))]
          refine lintegral_congr_ae ?_
          filter_upwards [aM] with m hm
          rw [hmul s hs m hm, mul_assoc, mul_assoc]
  let P : Subgroup G :=
    { carrier := {g | ∃ u ∈ N, ∃ m ∈ M, g = u * m}
      one_mem' := ⟨1, N.one_mem, 1, M.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨u, hu, m, hm, rfl⟩ ⟨u', hu', m', hm', rfl⟩
        exact ⟨u * (m * u' * m⁻¹), N.mul_mem hu (hnorm m hm u' hu'), m * m', M.mul_mem hm hm', by group⟩
      inv_mem' := by
        rintro _ ⟨u, hu, m, hm, rfl⟩
        exact ⟨m⁻¹ * u⁻¹ * m⁻¹⁻¹, hnorm _ (M.inv_mem hm) _ (N.inv_mem hu), m⁻¹, M.inv_mem hm, by group⟩ }
  have lP : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ := by
    rintro _ ⟨u, hu, m, hm, rfl⟩
    have : (fun g => u * m * g) = (fun g => u * g) ∘ (fun g => m * g) := by
      funext g; simp [mul_assoc]
    rw [this, ← Measure.map_map (measurable_const_mul u) (measurable_const_mul m), lM m hm, lN u hu]
  set Q : ℕ → Set G := fun i => (compactCovering G i ∩ N) * (compactCovering G i ∩ M) with hQ
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    ((isCompact_compactCovering G i).inter_right hN).mul ((isCompact_compactCovering G i).inter_right hM)
  have hQP : ∀ g ∈ P, ∃ i, g ∈ Q i := by
    rintro _ ⟨u, hu, m, hm, rfl⟩
    obtain ⟨i, hi⟩ := exists_mem_compactCovering u
    obtain ⟨j, hj⟩ := exists_mem_compactCovering m
    exact ⟨max i j, Set.mul_mem_mul ⟨compactCovering_subset G (le_max_left _ _) hi, hu⟩
      ⟨compactCovering_subset G (le_max_right _ _) hj, hm⟩⟩
  have hPm : MeasurableSet (P : Set G) := by
    have : (P : Set G) = ⋃ i, Q i := by
      ext g
      rw [Set.mem_iUnion]
      refine ⟨hQP g, ?_⟩
      rintro ⟨i, u, hu, m, hm, rfl⟩
      exact ⟨u, hu.2, m, hm.2, rfl⟩
    rw [this]
    exact MeasurableSet.iUnion fun i => (hQc i).measurableSet
  have hP0 : ρ (P : Set G)ᶜ = 0 := by
    rw [← lintegral_indicator_one hPm.compl, hρ _ (measurable_one.indicator hPm.compl)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aN] with u hu
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aM] with m hm
    rw [Set.indicator_of_notMem (show u * m ∉ (P : Set G)ᶜ from fun h => h ⟨u, hu, m, hm, rfl⟩)]
    simp
  set T : ℕ → Set G := fun i => (K : Set G) * Q i with hT
  have hTc : ∀ i, IsCompact (T i) := fun i => hK.mul (hQc i)
  have hTu : ⋃ i, T i = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ?_
    obtain ⟨u, hu, m, hm, k, hk, h⟩ := hdec g⁻¹
    obtain ⟨i, hi⟩ := hQP _ (P.inv_mem ⟨u, hu, m, hm, rfl⟩)
    refine ⟨i, k⁻¹, K.inv_mem hk, _, hi, ?_⟩
    rw [← inv_inv g, h]
    simp only [mul_inv_rev]
  have hT1 : ∀ i, ρ (T i) < ⊤ := by
    intro i
    set B : Set G := (K : Set G) * compactCovering G i with hB
    have hBc : IsCompact B := hK.mul (isCompact_compactCovering G i)
    have hAc : IsCompact (B * (K : Set G)) := hBc.mul hK
    have hRc : IsCompact (B⁻¹ * C * B) := (hBc.inv.mul hC).mul hBc
    set R := μN (B⁻¹ * C * B) / μN C with hR
    have hR1 : R < ⊤ := ENNReal.div_lt_top hRc.measure_lt_top.ne hC0
    have hb : ∀ m ∈ M, m ∈ B → δ m ≤ R := by
      intro m hm hmB
      rw [hR, ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hC1), ← hval m hm C hC.measurableSet]
      refine measure_mono fun u hu => ?_
      have : u = m⁻¹ * (m * u * m⁻¹) * m := by group
      rw [this]
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.inv_mem_inv.2 hmB) hu) hmB
    have hmem : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ T i → u ∈ B * (K : Set G) ∧ m ∈ B := by
      rintro u hu m hm ⟨k, hk, _, ⟨u', hu', m', hm', rfl⟩, h⟩
      have h : k * (u' * m') = u * m := h
      have hm'' : m * m'⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hm'.2)
      have e : u * (m * m'⁻¹ * u'⁻¹ * (m * m'⁻¹)⁻¹) * (m * m'⁻¹) = k := by
        calc _ = u * m * (u' * m')⁻¹ := by group
          _ = k := by rw [← h]; group
      have e1 := huniq _ (N.mul_mem hu (hnorm _ hm'' _ (N.inv_mem hu'.2))) _ hm'' (by rw [e]; exact hk)
      rw [e1, one_mul] at e
      have em : m = k * m' := by rw [← e]; group
      have eu : u = k * u' * k⁻¹ := by
        calc u = u * m * m⁻¹ := by group
          _ = _ := by rw [← h, em]; group
      refine ⟨?_, ?_⟩
      · rw [eu]; exact Set.mul_mem_mul (Set.mul_mem_mul hk hu'.1) (K.inv_mem hk)
      · rw [em]; exact Set.mul_mem_mul hk hm'.1
    rw [← lintegral_indicator_one (hTc i).measurableSet, hρ _ (measurable_one.indicator (hTc i).measurableSet)]
    calc _ ≤ ∫⁻ u, (B * (K : Set G)).indicator (fun _ => R * μM B) u ∂μN := by
          refine lintegral_mono_ae ?_
          filter_upwards [aN] with u hu
          by_cases hA : u ∈ B * (K : Set G)
          · rw [Set.indicator_of_mem hA, ← lintegral_indicator_const hBc.measurableSet]
            refine lintegral_mono_ae ?_
            filter_upwards [aM] with m hm
            by_cases hum : u * m ∈ T i
            · rw [Set.indicator_of_mem hum, Set.indicator_of_mem (hmem u hu m hm hum).2]
              simpa using hb m hm (hmem u hu m hm hum).2
            · rw [Set.indicator_of_notMem hum]; simp
          · rw [Set.indicator_of_notMem hA]
            refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
            filter_upwards [aM] with m hm
            rw [Set.indicator_of_notMem (fun h => hA (hmem u hu m hm h).1)]
            simp
      _ < ⊤ := by
          rw [lintegral_indicator_const hAc.measurableSet]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hR1 hBc.measure_lt_top) hAc.measure_lt_top
  haveI : SigmaFinite ρ := ⟨⟨⟨T, fun _ => trivial, hT1, hTu⟩⟩⟩
  have hρ0 : ρ Set.univ ≠ 0 := by
    rw [← lintegral_one, hρ _ measurable_const]
    simp only [mul_one, lintegral_const]
    refine mul_ne_zero (fun h => hM0 ?_) hN0
    rw [lintegral_eq_zero_iff hδ] at h
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h, aM] with m h hm using hδ0 m hm h
  obtain ⟨i, hi⟩ : ∃ i, ρ (T i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hρ0 (by rw [← hTu]; exact measure_iUnion_null h)
  have hTK : ∀ k ∈ K, ∀ g, g ∈ T i → k * g ∈ T i := by
    rintro k hk _ ⟨k', hk', x, hx, rfl⟩
    exact ⟨k * k', K.mul_mem hk hk', x, hx, mul_assoc _ _ _⟩
  obtain ⟨c, hc0, hc1, hc⟩ := exists_lintegral_eq_mul μ ρ μK hμ P K iK lP
    (exists_map_mul_right_eq_smul P hPm ρ hP0 lP (T i) (hTc i).measurableSet hi (hT1 i).ne)
    (fun g => by
      obtain ⟨u, hu, m, hm, k, hk, h⟩ := hdec g
      exact ⟨u * m, ⟨u, hu, m, hm, rfl⟩, k, hk, h⟩)
    (T i) (hTc i).measurableSet
    (fun k hk g => ⟨fun h => by simpa using hTK k hk _ h, hTK _ (K.inv_mem hk) g⟩) hi (hT1 i).ne
  refine ⟨c, hc0, hc1, fun φ hφ => ?_⟩
  rw [hc φ hφ, hρ _ (Measurable.lintegral_prod_right' (f := fun z : G × G => φ (z.1 * z.2))
    (hφ.comp measurable_mul))]
end GlobalTheory.IwasawaShape
