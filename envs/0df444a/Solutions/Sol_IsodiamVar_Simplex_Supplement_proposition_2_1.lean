-- Prove2me | solution 1 for IsodiamVar.Simplex.Supplement.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:37.806493+00:00
-- url     : https://prove2.me/submissions/fa099dcc-ce5a-4458-90a8-c73c308beb7e

import Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre
import Definitions.Def_IsodiamVar_Simplex_Supplement_ZeroMean

open MeasureTheory

open IsodiamVar
open IsodiamVar.Simplex
open IsodiamVar.Simplex.Supplement

/-- Proposition 2.1, p. 8; proof pp. 9–11. Empty and infeasible cases use EReal. -/
theorem solution {n : ℕ} (K : Set (E n)) (hK : IsCompact K) :
    let primal : EReal := ⨆ μ : {μ : Measure (E n) // InP0 K μ},
      ((∫ x, ‖x‖ ^ 2 ∂μ.val : ℝ) : EReal)
    let dual : EReal := ⨅ q : E n, phiStar K ((-2 : ℝ) • q)
    primal = dual ∧ dual = -phiBiconjugate K 0 ∧
    (0 ∈ closedConvexHull ℝ K →
      ∃ μ : Measure (E n), InP0 K μ ∧ ((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) = primal) ∧
    (0 ∈ interior (closedConvexHull ℝ K) →
      ∃ q : E n, phiStar K ((-2 : ℝ) • q) = dual) ∧
    (∀ μ : Measure (E n), InP0 K μ → ∀ q : E n,
      ((((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) = primal ∧
          phiStar K ((-2 : ℝ) • q) = dual) ↔
        ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
          (∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall q r → R ≤ r) ∧
          μ (K ∩ Metric.sphere q R) = 1)) := by
            classical
            have hstar (p : E n) : phiStar K p =
                ⨆ x : K, (((inner ℝ p x.val + ‖x.val‖ ^ 2) : ℝ) : EReal) := by
              unfold phiStar WassersteinDRO.ConvexLossP1.conjugate phi
              apply le_antisymm
              · apply iSup_le
                intro x
                by_cases hx : x ∈ K
                · simp only [if_pos hx, innerSL_apply_apply]
                  simpa only [← EReal.coe_neg, ← EReal.coe_sub, ← EReal.coe_add, sub_neg_eq_add] using (le_iSup (fun y : K =>
                    (((inner ℝ p y.val + ‖y.val‖ ^ 2) : ℝ) : EReal)) ⟨x, hx⟩)
                · simp [hx]
              · apply iSup_le
                intro x
                have := le_iSup (fun y : E n =>
                  ((innerSL ℝ p y : ℝ) : EReal) -
                    if y ∈ K then ((-(‖y‖ ^ 2) : ℝ) : EReal) else ⊤) x.val
                simpa only [if_pos x.property, innerSL_apply_apply, ← EReal.coe_neg, ← EReal.coe_sub, sub_neg_eq_add] using this
            have hdual : (⨅ q : E n, phiStar K ((-2 : ℝ) • q)) =
                -phiBiconjugate K 0 := by
              unfold phiBiconjugate WassersteinDRO.ConvexLossP1.conjugate
              simp only [map_zero, zero_apply, EReal.coe_zero, sub_eq_add_neg, zero_add]
              rw [show -(⨆ p : E n, -phiStar K p) = ⨅ p : E n, phiStar K p from
                by
                  have hh := EReal.negOrderIso.map_iSup (fun p : E n => -phiStar K p)
                  change -(⨆ p : E n, -phiStar K p) = ⨅ p : E n, -(-phiStar K p) at hh
                  simpa only [neg_neg] using hh]
              apply le_antisymm
              · apply le_iInf
                intro p
                exact iInf_le_of_le ((- (1 / 2 : ℝ)) • p) (by simp [smul_smul])
              · apply le_iInf
                intro q
                exact iInf_le _ _
            have hInt {F : Type} [NormedAddCommGroup F] (μ : Measure (E n))
                (hμ : InP K μ) (f : E n → F) (hf : Continuous f) : Integrable f μ := by
              letI := hμ.1
              have ha : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hμ.2
              rw [← Measure.restrict_eq_self_of_ae_mem ha]
              exact ContinuousOn.integrableOn_compact hK hf.continuousOn
            have hne (μ : Measure (E n)) (hμ : InP K μ) : K.Nonempty := by
              letI := hμ.1
              exact (ae_iff.mpr hμ.2 : ∀ᵐ x ∂μ, x ∈ K).exists
            have hmax (p : E n) (hne : K.Nonempty) :
                ∃ a : ℝ, phiStar K p = (a : EReal) ∧
                  (∀ x ∈ K, inner ℝ p x + ‖x‖ ^ 2 ≤ a) ∧
                  ∃ x ∈ K, inner ℝ p x + ‖x‖ ^ 2 = a := by
              obtain ⟨x, hx, hm⟩ := hK.exists_isMaxOn hne
                (show ContinuousOn (fun x : E n => inner ℝ p x + ‖x‖ ^ 2) K by fun_prop)
              refine ⟨inner ℝ p x + ‖x‖ ^ 2, ?_, hm, x, hx, rfl⟩
              rw [hstar]
              apply le_antisymm
              · exact iSup_le fun y => EReal.coe_le_coe_iff.mpr (hm y.property)
              · exact le_iSup_of_le ⟨x, hx⟩ le_rfl
            letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
            have hIK {F : Type} [NormedAddCommGroup F] (ν : Measure K) [IsFiniteMeasure ν]
                (f : K → F) (hf : Continuous f) : Integrable f ν := by
              simpa using (ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn :
                IntegrableOn f Set.univ ν)
            let M : ProbabilityMeasure K → E n × ℝ := fun ν =>
              (∫ x : K, (x : E n) ∂(ν : Measure K), ∫ x : K, ‖(x : E n)‖ ^ 2 ∂(ν : Measure K))
            let C : Set (E n × ℝ) := Set.range M
            have hMc : Continuous M := by
              apply Continuous.prodMk
              · apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toHomeomorph.comp_continuous_iff.mp
                apply continuous_pi
                intro i
                have hh := ProbabilityMeasure.continuous_integral_continuousMap
                  (⟨fun x : K => (x : E n) i, by fun_prop⟩ : C(K, ℝ))
                convert hh using 1
                ext ν
                exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).integral_comp_comm
                  (hIK (ν : Measure K) _ continuous_subtype_val)).symm
              · exact ProbabilityMeasure.continuous_integral_continuousMap
                  (⟨fun x : K => ‖(x : E n)‖ ^ 2, by fun_prop⟩ : C(K, ℝ))
            have hCc : IsCompact C := isCompact_range hMc
            have hCv : Convex ℝ C := by
              rintro y ⟨μ, rfl⟩ z ⟨ν, rfl⟩ a b ha hb hab
              let ρ : Measure K := ENNReal.ofReal a • (μ : Measure K) + ENNReal.ofReal b • (ν : Measure K)
              have hρ : IsProbabilityMeasure ρ := by
                constructor
                simp only [ρ, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
                rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
              refine ⟨⟨ρ, hρ⟩, ?_⟩
              have hμ1 := hIK (μ : Measure K) (fun x : K => (x : E n)) continuous_subtype_val
              have hν1 := hIK (ν : Measure K) (fun x : K => (x : E n)) continuous_subtype_val
              have hμ2 := hIK (μ : Measure K) (fun x : K => ‖(x : E n)‖ ^ 2) (by fun_prop)
              have hν2 := hIK (ν : Measure K) (fun x : K => ‖(x : E n)‖ ^ 2) (by fun_prop)
              change (∫ x : K, (x : E n) ∂ρ, ∫ x : K, ‖(x : E n)‖ ^ 2 ∂ρ) =
                a • M μ + b • M ν
              dsimp only [ρ, M]
              rw [integral_add_measure (hμ1.smul_measure ENNReal.ofReal_ne_top)
                  (hν1.smul_measure ENNReal.ofReal_ne_top),
                integral_add_measure (hμ2.smul_measure ENNReal.ofReal_ne_top)
                  (hν2.smul_measure ENNReal.ofReal_ne_top)]
              simp [integral_smul_measure, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
            have hgraph (x : E n) (hx : x ∈ K) : (x, ‖x‖ ^ 2) ∈ C := by
              refine ⟨⟨Measure.dirac ⟨x, hx⟩, inferInstance⟩, ?_⟩
              simp [M]
            have hμC (μ : Measure (E n)) (hμ : InP K μ) :
                (barycenter μ, ∫ x, ‖x‖ ^ 2 ∂μ) ∈ C := by
              letI := hμ.1
              have hi := (hInt μ hμ (fun x => x) continuous_id).prodMk
                (hInt μ hμ (fun x => ‖x‖ ^ 2) (by fun_prop))
              have hh := hCv.integral_mem hCc.isClosed
                (show ∀ᵐ x ∂μ, (x, ‖x‖ ^ 2) ∈ C by
                  filter_upwards [ae_iff.mpr hμ.2] with x hx using hgraph x hx) hi
              rw [integral_pair hi.fst hi.snd] at hh
              exact hh
            have hCμ (y : E n × ℝ) (hy : y ∈ C) :
                ∃ μ : Measure (E n), InP K μ ∧ barycenter μ = y.1 ∧
                  (∫ x, ‖x‖ ^ 2 ∂μ) = y.2 := by
              obtain ⟨ν, rfl⟩ := hy
              let μ : Measure (E n) := Measure.map (Subtype.val : K → E n) ν
              have hip : InP K μ := by
                refine ⟨Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable, ?_⟩
                rw [Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet.compl]
                simp
              refine ⟨μ, hip, ?_, ?_⟩
              · exact integral_map measurable_subtype_coe.aemeasurable
                  continuous_id.aestronglyMeasurable
              · exact integral_map measurable_subtype_coe.aemeasurable
                  (show Continuous (fun x : E n => ‖x‖ ^ 2) by fun_prop).aestronglyMeasurable
            have hproj : Prod.fst '' C = closedConvexHull ℝ K := by
              apply Set.Subset.antisymm
              · rintro x ⟨y, hy, rfl⟩
                obtain ⟨μ, hμ, he, _⟩ := hCμ y hy
                letI := hμ.1
                rw [← he]
                exact (convex_closedConvexHull (𝕜 := ℝ) (s := K)).integral_mem
                  (isClosed_closedConvexHull (𝕜 := ℝ) (s := K))
                  (by filter_upwards [ae_iff.mpr hμ.2] with x hx using subset_closedConvexHull (𝕜 := ℝ) (s := K) hx)
                  (hInt μ hμ _ continuous_id)
              · apply closedConvexHull_min
                · intro x hx
                  exact ⟨(x, ‖x‖ ^ 2), hgraph x hx, rfl⟩
                · exact hCv.linear_image (LinearMap.fst ℝ (E n) ℝ)
                · exact (hCc.image continuous_fst).isClosed
            have hCstar (p : E n) :
                (⨆ y ∈ C, (((inner ℝ p y.1 + y.2) : ℝ) : EReal)) = phiStar K p := by
              apply le_antisymm
              · apply iSup₂_le
                intro y hy
                obtain ⟨ν, rfl⟩ := hy
                have hneK : K.Nonempty := by
                  obtain ⟨x, _⟩ := (Filter.Eventually.of_forall (fun x : K => True.intro) : ∀ᵐ x ∂(ν : Measure K), True).exists
                  exact ⟨x.val, x.property⟩
                obtain ⟨a, ha, hb, _⟩ := hmax p hneK
                rw [ha, EReal.coe_le_coe_iff]
                have hid := hIK (ν : Measure K) (fun x : K => (x : E n)) continuous_subtype_val
                have hin := hIK (ν : Measure K) (fun x : K => inner ℝ p (x : E n)) (by fun_prop)
                have his := hIK (ν : Measure K) (fun x : K => ‖(x : E n)‖ ^ 2) (by fun_prop)
                change inner ℝ p (∫ x : K, (x : E n) ∂(ν : Measure K)) +
                  (∫ x : K, ‖(x : E n)‖ ^ 2 ∂(ν : Measure K)) ≤ a
                rw [← integral_inner hid, ← integral_add hin his]
                simpa using integral_mono_ae (hin.add his) (integrable_const a)
                  (Filter.Eventually.of_forall fun x : K => hb x.val x.property)
              · rw [hstar]
                apply iSup_le
                intro x
                exact le_iSup₂_of_le (x.val, ‖x.val‖ ^ 2) (hgraph x.val x.property) le_rfl
            let L : (E n × ℝ) → E n → EReal := fun y p =>
              (((inner ℝ p y.1 + y.2) : ℝ) : EReal)
            have hsion : (⨆ y ∈ C, ⨅ p : E n, L y p) =
                ⨅ p : E n, ⨆ y ∈ C, L y p := by
              by_cases hCN : C.Nonempty
              · have hc (p : E n) : Continuous (fun y : E n × ℝ => L y p) := by
                  exact continuous_coe_real_ereal.comp (by fun_prop)
                have hp (y : E n × ℝ) : Continuous (fun p : E n => L y p) := by
                  exact continuous_coe_real_ereal.comp (by fun_prop)
                have hqc (p : E n) : QuasiconcaveOn ℝ C (fun y : E n × ℝ => L y p) := by
                  let l : (E n × ℝ) →ₗ[ℝ] ℝ :=
                    (innerSL ℝ p).toLinearMap.comp (LinearMap.fst ℝ (E n) ℝ) + LinearMap.snd ℝ (E n) ℝ
                  change QuasiconcaveOn ℝ C ((fun a : ℝ => (a : EReal)) ∘ l)
                  exact (l.concaveOn hCv).quasiconcaveOn.monotone_comp EReal.coe_strictMono.monotone
                have hqp (y : E n × ℝ) : QuasiconvexOn ℝ Set.univ (fun p : E n => L y p) := by
                  have hh := (((innerSL ℝ y.1).toLinearMap.convexOn convex_univ).add_const y.2).quasiconvexOn
                  have he := hh.monotone_comp (g := fun a : ℝ => (a : EReal)) EReal.coe_strictMono.monotone
                  change QuasiconvexOn ℝ Set.univ (fun p : E n => ((inner ℝ y.1 p + y.2 : ℝ) : EReal)) at he
                  simpa only [L, real_inner_comm] using he
                have hh := Sion.minimax' (β := ERealᵒᵈ) (f := fun y p => (L y p : ERealᵒᵈ))
                  hCN hCv hCc
                  (fun p _ => (hc p).continuousOn.upperSemicontinuousOn)
                  (fun p _ => hqc p) convex_univ
                  (fun y _ => (hp y).continuousOn.lowerSemicontinuousOn)
                  (fun y _ => hqp y)
                change (⨆ y ∈ C, ⨅ p ∈ (Set.univ : Set (E n)), L y p) =
                  ⨅ p ∈ (Set.univ : Set (E n)), ⨆ y ∈ C, L y p at hh
                simpa only [Set.mem_univ, iInf_true] using hh
              · have he : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCN
                simp [he]
            have hLinf (y : E n × ℝ) : (⨅ p : E n, L y p) =
                if y.1 = 0 then (y.2 : EReal) else ⊥ := by
              by_cases hy : y.1 = 0
              · simp [L, hy]
              · rw [if_neg hy]
                apply (EReal.eq_bot_iff_forall_lt _).mpr
                intro c
                have hn : ‖y.1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hy)
                let p : E n := ((c - 1 - y.2) / ‖y.1‖ ^ 2) • y.1
                have he : L y p = ((c - 1 : ℝ) : EReal) := by
                  dsimp [L, p]
                  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hn]
                  exact congrArg (fun a : ℝ => (a : EReal)) (by ring)
                exact (iInf_le (fun p => L y p) p).trans_lt (by rw [he, EReal.coe_lt_coe_iff]; linarith)
            have hprimal : (⨆ μ : {μ : Measure (E n) // InP0 K μ},
                ((∫ x, ‖x‖ ^ 2 ∂μ.val : ℝ) : EReal)) = ⨆ y ∈ C, ⨅ p : E n, L y p := by
              apply le_antisymm
              · apply iSup_le
                intro μ
                have hy := hμC μ.val μ.property.1
                have hz := μ.property.2
                rw [hz] at hy
                apply le_iSup₂_of_le (0, ∫ x, ‖x‖ ^ 2 ∂μ.val) hy
                simp [L]
              · apply iSup₂_le
                intro y hy
                rw [hLinf]
                split_ifs with hz
                · obtain ⟨μ, hμ, hm, hv⟩ := hCμ y hy
                  have h0 : InP0 K μ := ⟨hμ, hm.trans hz⟩
                  exact hv ▸ le_iSup (fun μ : {μ : Measure (E n) // InP0 K μ} =>
                    ((∫ x, ‖x‖ ^ 2 ∂μ.val : ℝ) : EReal)) ⟨μ, h0⟩
                · exact bot_le
            have hstrong : (⨆ μ : {μ : Measure (E n) // InP0 K μ},
                ((∫ x, ‖x‖ ^ 2 ∂μ.val : ℝ) : EReal)) =
                ⨅ q : E n, phiStar K ((-2 : ℝ) • q) := by
              rw [hprimal, hsion]
              change (⨅ p : E n, ⨆ y ∈ C, (((inner ℝ p y.1 + y.2) : ℝ) : EReal)) = _
              simp_rw [hCstar]
              apply le_antisymm
              · exact le_iInf fun q => iInf_le _ _
              · apply le_iInf
                intro p
                exact iInf_le_of_le ((-(1 / 2 : ℝ)) • p) (by simp [smul_smul])
            have hattain (hz : (0 : E n) ∈ closedConvexHull ℝ K) :
                ∃ μ : Measure (E n), InP0 K μ ∧
                  ((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) =
                    ⨆ μ : {μ : Measure (E n) // InP0 K μ},
                      ((∫ x, ‖x‖ ^ 2 ∂μ.val : ℝ) : EReal) := by
              let D : Set (E n × ℝ) := C ∩ {y | y.1 = 0}
              have hDc : IsCompact D := hCc.inter_right (isClosed_eq continuous_fst continuous_const)
              have hDn : D.Nonempty := by
                rw [← hproj] at hz
                obtain ⟨y, hy, hy0⟩ := hz
                exact ⟨y, hy, hy0⟩
              obtain ⟨y, hy, hm⟩ := hDc.exists_isMaxOn hDn continuous_snd.continuousOn
              obtain ⟨μ, hμ, hmb, hmv⟩ := hCμ y hy.1
              have hμ0 : InP0 K μ := ⟨hμ, hmb.trans hy.2⟩
              refine ⟨μ, hμ0, le_antisymm (le_iSup_of_le ⟨μ, hμ0⟩ le_rfl) ?_⟩
              apply iSup_le
              intro ν
              apply EReal.coe_le_coe_iff.mpr
              rw [hmv]
              exact hm ⟨hμC ν.val ν.property.1, ν.property.2⟩
            have hdualAttain (hz : (0 : E n) ∈ interior (closedConvexHull ℝ K)) :
                ∃ q : E n, phiStar K ((-2 : ℝ) • q) = ⨅ q : E n, phiStar K ((-2 : ℝ) • q) := by
              obtain ⟨μ, hμ, _⟩ := hattain (interior_subset hz)
              have hKN := hne μ hμ.1
              obtain ⟨a0, ha0, hb0, _⟩ := hmax 0 hKN
              have ha0n : 0 ≤ a0 := by
                obtain ⟨x, hx⟩ := hKN
                have hh := hb0 x hx
                simp only [inner_zero_left, zero_add] at hh
                exact (sq_nonneg _).trans hh
              obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
              have hls : LowerSemicontinuous (phiStar K) := by
                have he : phiStar K = fun p => ⨆ x : K,
                    (((inner ℝ p x.val + ‖x.val‖ ^ 2) : ℝ) : EReal) := funext hstar
                rw [he]
                exact lowerSemicontinuous_iSup fun x =>
                  (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
              let S : Set (E n) := {p | phiStar K p ≤ phiStar K 0}
              have hSc : IsClosed S := hls.isClosed_preimage _
              have hSb : Bornology.IsBounded S := by
                apply (isBounded_iff_forall_norm_le).mpr
                refine ⟨2 * a0 / ε, ?_⟩
                intro p hp
                by_cases hp0 : p = 0
                · simp only [hp0, norm_zero]
                  positivity
                obtain ⟨a, ha, hb, _⟩ := hmax p hKN
                have haa0 : a ≤ a0 := by
                  have hh : phiStar K p ≤ phiStar K 0 := hp
                  rwa [ha, ha0, EReal.coe_le_coe_iff] at hh
                have hsup : ∀ x ∈ closedConvexHull ℝ K, inner ℝ p x ≤ a := by
                  apply closedConvexHull_min (t := {x : E n | inner ℝ p x ≤ a})
                  · intro x hx
                    change inner ℝ p x ≤ a
                    have hh := hb x hx
                    linarith [sq_nonneg ‖x‖]
                  · intro x hx y hy c d hc hd hcd
                    change inner ℝ p (c • x + d • y) ≤ a
                    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
                    calc
                      _ ≤ c * a + d * a := add_le_add
                        (mul_le_mul_of_nonneg_left hx hc) (mul_le_mul_of_nonneg_left hy hd)
                      _ = a := by nlinarith
                  · exact isClosed_le (show Continuous (fun x : E n => inner ℝ p x) by fun_prop) continuous_const
                have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
                let y : E n := (ε / 2 / ‖p‖) • p
                have hny : ‖y‖ = ε / 2 := by
                  rw [norm_smul_of_nonneg (by positivity : 0 ≤ ε / 2 / ‖p‖)]
                  exact div_mul_cancel₀ _ hn.ne'
                have hy : y ∈ closedConvexHull ℝ K := hεK (by
                  simp only [Metric.mem_ball, dist_zero_right, hny]
                  linarith)
                have hiy : inner ℝ p y = ε / 2 * ‖p‖ := by
                  dsimp [y]
                  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
                  field_simp
                have hh := hsup y hy
                rw [hiy] at hh
                apply (le_div_iff₀ hε).mpr
                nlinarith
              have hSK : IsCompact S := (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hSc, hSb⟩
              obtain ⟨p, hpS, hpmin⟩ := (hls.lowerSemicontinuousOn S).exists_isMinOn
                (show S.Nonempty from ⟨0, by change phiStar K 0 ≤ phiStar K 0; exact le_rfl⟩) hSK
              have hpall (p' : E n) : phiStar K p ≤ phiStar K p' := by
                by_cases hp' : p' ∈ S
                · exact hpmin hp'
                · exact le_trans hpS (le_of_not_ge hp')
              refine ⟨(-(1 / 2 : ℝ)) • p, ?_⟩
              simp only [smul_smul]
              norm_num
              exact le_antisymm (le_iInf fun q => hpall _) (iInf_le_of_le ((-(1 / 2 : ℝ)) • p) (by simp [smul_smul]))
            have hgeom (q x : E n) : inner ℝ ((-2 : ℝ) • q) x + ‖x‖ ^ 2 =
                dist x q ^ 2 - ‖q‖ ^ 2 := by
              rw [real_inner_smul_left, dist_eq_norm, norm_sub_sq_real, real_inner_comm x q]
              ring
            have hball (μ : Measure (E n)) (hμ : InP0 K μ) (q : E n) :
                (((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) = phiStar K ((-2 : ℝ) • q)) ↔
                ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
                  (∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall q r → R ≤ r) ∧
                  μ (K ∩ Metric.sphere q R) = 1 := by
              letI := hμ.1.1
              let p : E n := (-2 : ℝ) • q
              obtain ⟨a, ha, hb, x0, hx0, hx0a⟩ := hmax p (hne μ hμ.1)
              have hid := hInt μ hμ.1 (fun x => x) continuous_id
              have hin := hInt μ hμ.1 (fun x => inner ℝ p x) (by fun_prop)
              have his := hInt μ hμ.1 (fun x => ‖x‖ ^ 2) (by fun_prop)
              have hmean : (∫ x, inner ℝ p x + ‖x‖ ^ 2 ∂μ) = ∫ x, ‖x‖ ^ 2 ∂μ := by
                rw [integral_add hin his, integral_inner hid, show (∫ x, x ∂μ) = 0 from hμ.2]
                simp
              have hsateq : (∫ x, ‖x‖ ^ 2 ∂μ) = a ↔
                  ∀ᵐ x ∂μ, inner ℝ p x + ‖x‖ ^ 2 = a := by
                rw [← hmean]
                have hh := integral_eq_iff_of_ae_le (f := fun x => inner ℝ p x + ‖x‖ ^ 2)
                  (g := fun _ => a) (hin.add his) (integrable_const a)
                  (by filter_upwards [ae_iff.mpr hμ.1.2] with x hx using hb x hx)
                rw [integral_const, show μ.real Set.univ = 1 from probReal_univ, one_smul] at hh
                exact hh
              change (((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) = phiStar K p) ↔ _
              rw [ha, EReal.coe_eq_coe_iff, hsateq]
              constructor
              · intro he
                have han : 0 ≤ a + ‖q‖ ^ 2 := by
                  have hh := hgeom q x0
                  change inner ℝ p x0 + ‖x0‖ ^ 2 = _ at hh
                  rw [hx0a] at hh
                  nlinarith [sq_nonneg (dist x0 q)]
                let R : ℝ := Real.sqrt (a + ‖q‖ ^ 2)
                have hR : 0 ≤ R := Real.sqrt_nonneg _
                have hRs : R ^ 2 = a + ‖q‖ ^ 2 := Real.sq_sqrt han
                have hdist0 : dist x0 q = R := by
                  have hh := hgeom q x0
                  change inner ℝ p x0 + ‖x0‖ ^ 2 = _ at hh
                  rw [hx0a] at hh
                  nlinarith [dist_nonneg (x := x0) (y := q)]
                refine ⟨R, hR, ?_, ?_, ?_⟩
                · intro x hx
                  rw [Metric.mem_closedBall]
                  have hh := hb x hx
                  rw [hgeom q x] at hh
                  nlinarith [dist_nonneg (x := x) (y := q)]
                · intro r hr hKr
                  have hh := hKr hx0
                  rw [Metric.mem_closedBall, hdist0] at hh
                  exact hh
                · apply (mem_ae_iff_prob_eq_one
                    (hK.isClosed.measurableSet.inter (Metric.isClosed_sphere.measurableSet))).mp
                  filter_upwards [ae_iff.mpr hμ.1.2, he] with x hx hxe
                  refine ⟨hx, ?_⟩
                  rw [Metric.mem_sphere]
                  have hh := hgeom q x
                  change inner ℝ p x + ‖x‖ ^ 2 = _ at hh
                  rw [hxe] at hh
                  nlinarith [dist_nonneg (x := x) (y := q)]
              · rintro ⟨R, hR, hKR, _, hmass⟩
                have hae : ∀ᵐ x ∂μ, x ∈ K ∩ Metric.sphere q R :=
                  (mem_ae_iff_prob_eq_one
                    (hK.isClosed.measurableSet.inter (Metric.isClosed_sphere.measurableSet))).mpr hmass
                obtain ⟨x1, hx1⟩ := hae.exists
                have hx1R : dist x1 q = R := hx1.2
                have haeR : a = R ^ 2 - ‖q‖ ^ 2 := by
                  apply le_antisymm
                  · have hh := hKR hx0
                    rw [Metric.mem_closedBall] at hh
                    have h0 := hgeom q x0
                    change inner ℝ p x0 + ‖x0‖ ^ 2 = _ at h0
                    rw [hx0a] at h0
                    nlinarith [dist_nonneg (x := x0) (y := q)]
                  · have hh := hb x1 hx1.1
                    have h1 := hgeom q x1
                    change inner ℝ p x1 + ‖x1‖ ^ 2 = _ at h1
                    rw [hx1R] at h1
                    linarith
                filter_upwards [hae] with x hx
                rw [hgeom q x, show dist x q = R from hx.2, haeR]
            refine ⟨hstrong, hdual, hattain, hdualAttain, ?_⟩
            intro μ hμ q
            rw [← hball μ hμ q]
            constructor
            · rintro ⟨hm, hq⟩
              exact hm.trans (hstrong.trans hq.symm)
            · intro he
              have hlo : ((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) ≤
                  ⨆ ν : {ν : Measure (E n) // InP0 K ν}, ((∫ x, ‖x‖ ^ 2 ∂ν.val : ℝ) : EReal) :=
                le_iSup_of_le ⟨μ, hμ⟩ le_rfl
              have hhi : (⨅ q : E n, phiStar K ((-2 : ℝ) • q)) ≤ phiStar K ((-2 : ℝ) • q) :=
                iInf_le _ q
              exact ⟨le_antisymm hlo (by rw [he, hstrong]; exact hhi),
                le_antisymm (by rw [← he, ← hstrong]; exact hlo) hhi⟩
