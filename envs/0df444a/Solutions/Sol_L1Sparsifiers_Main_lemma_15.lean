-- Prove2me | solution 1 for L1Sparsifiers.Main.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:54:33.116631+00:00
-- url     : https://prove2.me/submissions/84edd86f-04c0-4d5f-824b-c544fba4665b

import Definitions.Def_L1Sparsifiers_Main_Zonotope

open MeasureTheory L1Sparsifiers.Main

namespace AuxLemma15

lemma segment_symm_eq {n : ℕ} (v : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    segment ℝ (-(u • v)) (u • v) = {w | ∃ c : ℝ, |c| ≤ u ∧ w = c • v} := by
  ext w
  simp only [segment, Set.mem_ofPred]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨(b - a) * u, ?_, ?_⟩
    · have habs : |b - a| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |(b - a) * u| = |b - a| * |u| := abs_mul _ _
        _ = |b - a| * u := by rw [abs_of_nonneg hu]
        _ ≤ 1 * u := mul_le_mul_of_nonneg_right habs hu
        _ = u := one_mul u
    · ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
  · rintro ⟨c, hc, rfl⟩
    by_cases hu0 : u = 0
    · have hc0 : c = 0 := abs_nonpos_iff.mp (hc.trans_eq hu0)
      subst hu0 hc0
      exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by simp⟩
    · have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hcu := abs_le.mp hc
      refine ⟨(u - c) / (2 * u), (u + c) / (2 * u),
        div_nonneg (by linarith) (by positivity),
        div_nonneg (by linarith) (by positivity),
        by field_simp [hu_pos.ne']; ring, ?_⟩
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp [hu_pos.ne']
      ring

/-! ### Shear equivalence on `ℝ × (Fin m → ℝ)` preserving Lebesgue measure -/

noncomputable def shearEquiv {m : ℕ} (σ : ℝ) (w : Fin m → ℝ) :
    (ℝ × (Fin m → ℝ)) ≃ₗ[ℝ] (ℝ × (Fin m → ℝ)) where
  toFun p := (p.1, p.2 - (p.1 / σ) • w)
  map_add' p q := by
    ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  map_smul' c p := by
    ext
    · rfl
    · simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  invFun p := (p.1, p.2 + (p.1 / σ) • w)
  left_inv p := by
    ext
    · rfl
    · simp
  right_inv p := by
    ext
    · rfl
    · simp

lemma volume_preimage_shearEquiv_symm {m : ℕ} (σ : ℝ) (w : Fin m → ℝ)
    {E : Set (ℝ × (Fin m → ℝ))} (hE : MeasurableSet E) :
    volume ((shearEquiv σ w).symm ⁻¹' E) = volume E := by
  have hcont : Continuous (shearEquiv σ w).symm :=
    LinearMap.continuous_of_finiteDimensional (shearEquiv σ w).symm.toLinearMap
  have hmeas_pre : MeasurableSet ((shearEquiv σ w).symm ⁻¹' E) := hcont.measurable hE
  rw [Measure.volume_eq_prod ℝ (Fin m → ℝ), Measure.prod_apply hmeas_pre, Measure.prod_apply hE]
  refine lintegral_congr (fun t => ?_)
  have hslice : Prod.mk t ⁻¹' ((shearEquiv σ w).symm ⁻¹' E) =
      (fun z : Fin m → ℝ => z + (t / σ) • w) ⁻¹' (Prod.mk t ⁻¹' E) := rfl
  rw [hslice, measure_preimage_add_right]

/-! ### 1D compact convex interval erosion -/

lemma toReal_ofReal_eq_max (x : ℝ) : (ENNReal.ofReal x).toReal = max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [ENNReal.toReal_ofReal hx, max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [ENNReal.ofReal_eq_zero.mpr hx', ENNReal.toReal_zero, max_eq_right hx']

lemma one_dim_erosion_vol {S : Set ℝ} (hSc : IsCompact S) (hScv : Convex ℝ S)
    {d : ℝ} (hd : 0 ≤ d) :
    (volume {t : ℝ | ∀ c : ℝ, |c| ≤ d → t + c ∈ S}).toReal =
      max ((volume S).toReal - 2 * d) 0 := by
  by_cases hne : S.Nonempty
  · set a : ℝ := sInf S
    set b : ℝ := sSup S
    have ha_mem : a ∈ S := hSc.sInf_mem hne
    have hb_mem : b ∈ S := hSc.sSup_mem hne
    have hS_eq : S = Set.Icc a b := by
      ext t
      constructor
      · intro ht
        exact ⟨csInf_le hSc.bddBelow ht, le_csSup hSc.bddAbove ht⟩
      · intro ht
        exact hScv.ordConnected.out ha_mem hb_mem ht
    have hab : a ≤ b := (Set.mem_Icc.mp (hS_eq ▸ ha_mem)).2
    have herod : {t : ℝ | ∀ c : ℝ, |c| ≤ d → t + c ∈ S} = Set.Icc (a + d) (b - d) := by
      rw [hS_eq]
      ext t
      simp only [Set.mem_ofPred, Set.mem_Icc]
      constructor
      · intro h
        have h1 := (h (-d) (by rw [abs_neg, abs_of_nonneg hd])).1
        have h2 := (h d (by rw [abs_of_nonneg hd])).2
        exact ⟨by linarith, by linarith⟩
      · intro ⟨h1, h2⟩ c hc
        have hcd := abs_le.mp hc
        exact ⟨by linarith, by linarith⟩
    rw [herod, hS_eq, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), toReal_ofReal_eq_max]
    congr 1
    ring
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have herod_empty : {t : ℝ | ∀ c : ℝ, |c| ≤ d → t + c ∈ S} = ∅ := by
      rw [hne]
      ext t
      simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, by simpa using hd, not_false⟩
    rw [herod_empty, hne, measure_empty, ENNReal.toReal_zero]
    exact (max_eq_right (by linarith)).symm

end AuxLemma15

theorem solution {n : ℕ} (K : Set (Fin n → ℝ)) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (v : Fin n → ℝ) :
    ConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun s : ℝ => (volume (minkowskiSub K (segment ℝ (-(s • v)) (s • v)))).toReal) := by
  by_cases hv0 : v = 0
  · subst hv0
    have hconst : ∀ s : ℝ, minkowskiSub K (segment ℝ (-(s • (0 : Fin n → ℝ))) (s • 0)) = K := by
      intro s
      simp only [smul_zero, neg_zero, segment_same]
      ext x
      simp [minkowskiSub]
    simp_rw [hconst]
    exact convexOn_const _ (convex_Ici 0)
  cases n with
  | zero =>
    exfalso
    exact hv0 (Subsingleton.elim v 0)
  | succ m =>
    have hex : ∃ i0 : Fin (m + 1), v i0 ≠ 0 := by
      by_contra h
      apply hv0
      ext i
      exact not_ne_iff.mp (fun hne => h ⟨i, hne⟩)
    obtain ⟨i0, hvi0⟩ := hex
    set σ : ℝ := v i0
    have hσ_ne : σ ≠ 0 := hvi0
    set r : ℝ := |σ|
    have hr_pos : 0 < r := abs_pos.mpr hσ_ne
    -- Split Fin (m + 1) → ℝ at coordinate i0
    let eP := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i0
    have hmp_eP_symm : MeasurePreserving eP.symm volume volume :=
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i0).symm
    let L_split : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin m → ℝ) :=
      { toFun := fun x => (x i0, i0.removeNth x)
        map_add' := fun x y => by ext <;> simp [Fin.removeNth]
        map_smul' := fun c x => by ext <;> simp [Fin.removeNth]
        invFun := fun p => i0.insertNth p.1 p.2
        left_inv := fun x => i0.insertNth_self_removeNth x
        right_inv := fun p => by
          apply Prod.ext
          · exact Fin.insertNth_apply_same (α := fun _ => ℝ) i0 p.1 p.2
          · exact Fin.removeNth_insertNth (α := fun _ => ℝ) i0 p.1 p.2 }
    have hL_split_symm_eq : (L_split.symm : ℝ × (Fin m → ℝ) → (Fin (m + 1) → ℝ)) = eP.symm := by
      ext p k
      simp [L_split, eP, MeasurableEquiv.piFinSuccAbove_symm_apply]
    let w : Fin m → ℝ := i0.removeNth v
    let S_lin := AuxLemma15.shearEquiv σ w
    let Φ : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin m → ℝ) := L_split.trans S_lin
    have hΦ_cont : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ.toLinearMap
    let Q : Set (ℝ × (Fin m → ℝ)) := Φ '' K
    have hQc : IsCompact Q := hKc.image hΦ_cont
    have hQcv : Convex ℝ Q := hKcv.linear_image Φ.toLinearMap
    have hΦv : Φ v = (σ, 0) := by
      change S_lin (L_split v) = (σ, 0)
      have hLv : L_split v = (σ, w) := rfl
      rw [hLv]
      apply Prod.ext
      · rfl
      · ext j
        simp [S_lin, AuxLemma15.shearEquiv, div_self hσ_ne]
    -- Characterize Φ '' minkowskiSub K (segment ...) for s ≥ 0
    let Q_erod : ℝ → Set (ℝ × (Fin m → ℝ)) := fun s =>
      {p : ℝ × (Fin m → ℝ) | ∀ c : ℝ, |c| ≤ s * r → (p.1 + c, p.2) ∈ Q}
    have hΦ_erod : ∀ {s : ℝ}, 0 ≤ s →
        Φ '' minkowskiSub K (segment ℝ (-(s • v)) (s • v)) = Q_erod s := by
      intro s hs
      have hseg := AuxLemma15.segment_symm_eq v hs
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩ c hc
        have hcr : |c / σ| ≤ s := by
          rw [abs_div]
          exact (div_le_iff₀ hr_pos).mpr hc
        have hy_mem : (c / σ) • v ∈ segment ℝ (-(s • v)) (s • v) := by
          rw [hseg]
          exact ⟨c / σ, hcr, rfl⟩
        have hxy : x + (c / σ) • v ∈ K := hx _ hy_mem
        have hmap : Φ (x + (c / σ) • v) = ((Φ x).1 + c, (Φ x).2) := by
          rw [map_add, map_smul, hΦv]
          apply Prod.ext
          · simp [div_mul_cancel₀ c hσ_ne]
          · ext j; simp
        rw [← hmap]
        exact ⟨x + (c / σ) • v, hxy, rfl⟩
      · intro hp
        refine ⟨Φ.symm p, ?_, Φ.apply_symm_apply p⟩
        intro y hy
        rw [hseg] at hy
        obtain ⟨c, hc, rfl⟩ := hy
        have hcr : |c * σ| ≤ s * r := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hc hr_pos.le
        obtain ⟨z, hzK, hzΦ⟩ := hp (c * σ) hcr
        have heq : Φ.symm p + c • v = z := by
          apply Φ.injective
          rw [map_add, Φ.apply_symm_apply, map_smul, hΦv, hzΦ]
          apply Prod.ext
          · simp
          · ext j; simp
        rwa [heq]
    have hQ_erod_compact : ∀ {s : ℝ}, 0 ≤ s → IsCompact (Q_erod s) := by
      intro s hs
      have hsub : Q_erod s ⊆ Q := by
        intro p hp
        simpa using hp 0 (by rw [abs_zero]; positivity)
      have hclosed : IsClosed (Q_erod s) := by
        have heq : Q_erod s = ⋂ (c : ℝ) (_ : |c| ≤ s * r),
            (fun p : ℝ × (Fin m → ℝ) => (p.1 + c, p.2)) ⁻¹' Q := by
          ext p; simp [Q_erod]
        rw [heq]
        exact isClosed_biInter (fun c _ =>
          hQc.isClosed.preimage ((continuous_fst.add continuous_const).prodMk continuous_snd))
      exact Metric.isCompact_of_isClosed_isBounded hclosed (hQc.isBounded.subset hsub)
    have hvol_eq_erod : ∀ {s : ℝ}, 0 ≤ s →
        volume (minkowskiSub K (segment ℝ (-(s • v)) (s • v))) = volume (Q_erod s) := by
      intro s hs
      have hmeas_erod : MeasurableSet (Q_erod s) := (hQ_erod_compact hs).isClosed.measurableSet
      have hmeas_K : MeasurableSet (minkowskiSub K (segment ℝ (-(s • v)) (s • v))) := by
        have heq : minkowskiSub K (segment ℝ (-(s • v)) (s • v)) = Φ ⁻¹' (Q_erod s) := by
          rw [← hΦ_erod hs]
          ext x; simp [Φ.injective.eq_iff]
        rw [heq]
        exact hΦ_cont.measurable hmeas_erod
      have hpre_split : S_lin.symm ⁻¹' (eP.symm ⁻¹' (minkowskiSub K (segment ℝ (-(s • v)) (s • v)))) =
          Q_erod s := by
        rw [← hL_split_symm_eq, ← hΦ_erod hs]
        ext p
        simp only [Set.mem_preimage, Set.mem_image]
        constructor
        · intro hp
          exact ⟨Φ.symm p, hp, Φ.apply_symm_apply p⟩
        · rintro ⟨x, hx, rfl⟩
          have hsymm : L_split.symm (S_lin.symm (Φ x)) = x := Φ.symm_apply_apply x
          rwa [hsymm]
      have hmeas_eP : MeasurableSet (eP.symm ⁻¹' (minkowskiSub K (segment ℝ (-(s • v)) (s • v)))) :=
        eP.symm.measurable hmeas_K
      calc volume (minkowskiSub K (segment ℝ (-(s • v)) (s • v)))
          = volume (eP.symm ⁻¹' (minkowskiSub K (segment ℝ (-(s • v)) (s • v)))) :=
              (hmp_eP_symm.measure_preimage hmeas_K.nullMeasurableSet).symm
        _ = volume (S_lin.symm ⁻¹' (eP.symm ⁻¹' (minkowskiSub K (segment ℝ (-(s • v)) (s • v))))) :=
              (AuxLemma15.volume_preimage_shearEquiv_symm σ w hmeas_eP).symm
        _ = volume (Q_erod s) := by rw [hpre_split]
    -- Express (volume (Q_erod s)).toReal via Fubini as ∫ y, max (len y - 2 * r * s) 0
    let len : (Fin m → ℝ) → ℝ := fun y => (volume {t : ℝ | (t, y) ∈ Q}).toReal
    have hslice_compact_convex : ∀ y : Fin m → ℝ,
        IsCompact {t : ℝ | (t, y) ∈ Q} ∧ Convex ℝ {t : ℝ | (t, y) ∈ Q} := by
      intro y
      have hcl : IsClosed {t : ℝ | (t, y) ∈ Q} :=
        hQc.isClosed.preimage (continuous_id.prodMk continuous_const)
      have hbd : Bornology.IsBounded {t : ℝ | (t, y) ∈ Q} := by
        have hsub : {t : ℝ | (t, y) ∈ Q} ⊆ Prod.fst '' Q := fun t ht => ⟨(t, y), ht, rfl⟩
        exact (hQc.image continuous_fst).isBounded.subset hsub
      refine ⟨Metric.isCompact_of_isClosed_isBounded hcl hbd, ?_⟩
      intro t1 ht1 t2 ht2 a b ha hb hab
      have h := hQcv ht1 ht2 ha hb hab
      have hfst : (a • (t1, y) + b • (t2, y)).1 = a • t1 + b • t2 := rfl
      have hsnd : (a • (t1, y) + b • (t2, y)).2 = y := by
        ext i; simp only [Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc a * y i + b * y i = (a + b) * y i := by ring
          _ = y i := by rw [hab, one_mul]
      have hpair : a • (t1, y) + b • (t2, y) = (a • t1 + b • t2, y) := Prod.ext hfst hsnd
      rwa [hpair] at h
    have hfubini : ∀ {s : ℝ}, 0 ≤ s →
        (volume (Q_erod s)).toReal = ∫ y : Fin m → ℝ, max (len y - 2 * r * s) 0 ∧
          Integrable (fun y : Fin m → ℝ => max (len y - 2 * r * s) 0) volume := by
      intro s hs
      have hQc_s := hQ_erod_compact hs
      have hmeas_s : MeasurableSet (Q_erod s) := hQc_s.isClosed.measurableSet
      have hfin_s : volume (Q_erod s) < ⊤ := hQc_s.measure_lt_top
      let g : ℝ × (Fin m → ℝ) → ℝ := (Q_erod s).indicator (fun _ => (1 : ℝ))
      have hg_int : Integrable g (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ (Fin m → ℝ)]
        exact (integrableOn_const hfin_s.ne).integrable_indicator hmeas_s
      have hslice_eq : ∀ y : Fin m → ℝ,
          ∫ t : ℝ, g (t, y) = max (len y - 2 * r * s) 0 := by
        intro y
        have hpre_s : (fun t : ℝ => (t, y)) ⁻¹' (Q_erod s) =
            {t : ℝ | ∀ c : ℝ, |c| ≤ s * r → t + c ∈ {u : ℝ | (u, y) ∈ Q}} := by
          ext t; simp [Q_erod]
        have hmeas_slice : MeasurableSet ((fun t : ℝ => (t, y)) ⁻¹' (Q_erod s)) :=
          (continuous_id.prodMk continuous_const).measurable hmeas_s
        have hind_eq : (fun t : ℝ => g (t, y)) =
            ((fun t : ℝ => (t, y)) ⁻¹' (Q_erod s)).indicator (fun _ => (1 : ℝ)) := by
          ext t
          by_cases ht : (t, y) ∈ Q_erod s <;> simp [g, ht]
        rw [hind_eq, MeasureTheory.integral_indicator hmeas_slice,
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real, hpre_s]
        obtain ⟨hSc, hScv⟩ := hslice_compact_convex y
        rw [AuxLemma15.one_dim_erosion_vol hSc hScv (mul_nonneg hs hr_pos.le)]
        congr 2
        ring
      have hint_y : Integrable (fun y : Fin m → ℝ => ∫ t : ℝ, g (t, y)) volume :=
        hg_int.integral_prod_right
      rw [funext hslice_eq] at hint_y
      refine ⟨?_, hint_y⟩
      calc (volume (Q_erod s)).toReal
          = ∫ p : ℝ × (Fin m → ℝ), g p := by
              simp only [g]
              rw [MeasureTheory.integral_indicator hmeas_s,
                MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
              rfl
        _ = ∫ p : ℝ × (Fin m → ℝ), g p ∂(volume.prod volume) := by
              rw [Measure.volume_eq_prod ℝ (Fin m → ℝ)]
        _ = ∫ y : Fin m → ℝ, ∫ t : ℝ, g (t, y) := MeasureTheory.integral_prod_symm g hg_int
        _ = ∫ y : Fin m → ℝ, max (len y - 2 * r * s) 0 := by simp_rw [hslice_eq]
    -- Prove ConvexOn on Set.Ici 0
    refine ⟨convex_Ici 0, ?_⟩
    intro s1 hs1 s2 hs2 a b ha hb hab
    have hs1' : 0 ≤ s1 := Set.mem_Ici.mp hs1
    have hs2' : 0 ≤ s2 := Set.mem_Ici.mp hs2
    have hcomb_nn : 0 ≤ a • s1 + b • s2 := by
      simp only [smul_eq_mul]; positivity
    obtain ⟨heq1, hint1⟩ := hfubini hs1'
    obtain ⟨heq2, hint2⟩ := hfubini hs2'
    obtain ⟨heq_c, hint_c⟩ := hfubini hcomb_nn
    dsimp only
    rw [hvol_eq_erod hcomb_nn, hvol_eq_erod hs1', hvol_eq_erod hs2',
      heq_c, heq1, heq2]
    simp only [smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul a, ← MeasureTheory.integral_const_mul b,
      ← MeasureTheory.integral_add (hint1.const_mul a) (hint2.const_mul b)]
    refine MeasureTheory.integral_mono hint_c ((hint1.const_mul a).add (hint2.const_mul b)) ?_
    intro y
    dsimp only [Pi.add_apply]
    have hlin : len y - 2 * r * (a * s1 + b * s2) =
        a * (len y - 2 * r * s1) + b * (len y - 2 * r * s2) := by
      calc len y - 2 * r * (a * s1 + b * s2)
          = (a + b) * len y - 2 * r * (a * s1 + b * s2) := by rw [hab, one_mul]
        _ = a * (len y - 2 * r * s1) + b * (len y - 2 * r * s2) := by ring
    rw [hlin]
    apply max_le
    · have h1 : a * (len y - 2 * r * s1) ≤ a * max (len y - 2 * r * s1) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) ha
      have h2 : b * (len y - 2 * r * s2) ≤ b * max (len y - 2 * r * s2) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hb
      linarith
    · positivity
