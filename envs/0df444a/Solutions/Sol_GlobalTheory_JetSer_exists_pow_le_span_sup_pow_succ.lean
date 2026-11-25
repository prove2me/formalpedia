-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:45.946257+00:00
-- url     : https://prove2.me/submissions/54f03daf-c6bf-4001-b48c-6fd1d366d4ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LocallyOfFiniteTypePullbackUnit
import Theorems.Thm_GlobalTheory_JetSer_mem_sup_pow_of_toJet_mem_map
import Theorems.Thm_GlobalTheory_JetSer_locallyOfFiniteType_pullback_unit
import Theorems.Thm_GlobalTheory_JetSer_isFPt_of_isUnivChart
import Theorems.Thm_GlobalTheory_JetSer_jetAlg
import Theorems.Thm_GlobalTheory_JetSer_jetAug_toJet
import Theorems.Thm_GlobalTheory_JetSer_repSt_of_jetAlgSt
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
import Theorems.Thm_GlobalTheory_T_exists_universal_thickening_of_finite_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (f : G ⟶ G), η[G] ≫ f = η[G] → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite {x : Over.mk t ⟶ G // x ≫ f = 1}) → ∀ (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ φ : Pt k 1 d, GlobalTheory.JetSer.IsMapOf x x f φ → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ M ≤ Ideal.span (Set.range φ) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ (M + 1) := by
  intro k _ G _ _ f hf hfin d x hx φ hφ
  haveI := locallyOfFiniteType_pullback_unit G f
  have hext : ∀ {T : Over (Spec (CommRingCat.of k))} (u v : T ⟶ pullback f η[G]),
      u ≫ pullback.fst f η[G] = v ≫ pullback.fst f η[G] → u = v := fun u v h =>
    pullback.hom_ext h (toUnit_unique _ _)
  have hfinK : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)),
      Finite (Over.mk t ⟶ pullback f η[G]) := by
    intro Ω _ _ t
    haveI := hfin Ω t
    refine Finite.of_injective (β := {x : Over.mk t ⟶ G // x ≫ f = 1})
      (fun u => ⟨u ≫ pullback.fst f η[G], ?_⟩) (fun u v h => hext u v (congrArg Subtype.val h))
    rw [Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h1f : (1 : Chart.sp (R₀ := k) k ⟶ G) ≫ f = toUnit _ ≫ η[G] := by
    rw [Hom.one_def, Category.assoc, hf]
  obtain ⟨A, _, _, aug, M, io, hM, hio, hU⟩ :=
    GlobalTheory.T.exists_universal_thickening_of_finite_points k (pullback f η[G]) hfinK (pullback.lift 1 (toUnit _) h1f)
  refine ⟨M + 1, ?_⟩
  obtain ⟨hex, -, hfp, -, -⟩ := repSt_of_jetAlgSt jetAlg k G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := hex (pt k (n := 1) d 0) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
  have hy' := hφ.2 1 _ y hy
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_pt_right] at hy'
  obtain ⟨ψ₀, hψ₀, hy₀⟩ := hy.2 (M + 1)
  obtain ⟨ψ₁, hψ₁, hy₁⟩ := hy'.2 (M + 1)
  have hya := (hfp _ y hy).2 (M + 1)
  have hxa := (isFPt_of_isUnivChart hx).2 (M + 1)
  set I : Ideal (Chart.JetR k (Fin 1 × Fin d) (M + 1)) :=
    (Ideal.span (Set.range φ)).map (toJetHom k (Fin 1 × Fin d) (M + 1)) with hI
  have hIle : I ≤ RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) := by
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (jetAug_toJet (M + 1) (φ j)).trans (hφ.1 j)
  let π := Ideal.Quotient.mkₐ k I
  let augQ : (Chart.JetR k (Fin 1 × Fin d) (M + 1) ⧸ I) →ₐ[k] k :=
    Ideal.Quotient.liftₐ I (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) (fun a ha => hIle ha)
  have haπ : augQ.comp π = Chart.jetAug k (Fin 1 × Fin d) (M + 1) := AlgHom.ext fun _ => rfl
  have hkQ : RingHom.ker augQ ^ (M + 1 + 1) = ⊥ := by
    have hle : RingHom.ker augQ ≤ (RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1))).map π := by
      intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact Ideal.mem_map_of_mem π hq
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, Chart.ker_jetAug_pow, Ideal.map_bot]
  have hz : (Chart.spMap π ≫ y (M + 1)) ≫ f = toUnit _ ≫ η[G] := by
    have e : π.comp ψ₁ = (Algebra.ofId k _).comp (Chart.jetAug k (Fin d) (M + 1)) := by
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero, hψ₁]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_map_of_mem (toJetHom k (Fin 1 × Fin d) (M + 1)) (Ideal.subset_span ⟨j, rfl⟩))
    have hy₁' : y (M + 1) ≫ f = Chart.spMap ψ₁ ≫ x (M + 1) := hy₁
    rw [Category.assoc, hy₁', ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hxa,
      ← Hom.one_def]
    exact MonObj.comp_one _
  have hzone : Chart.spMap augQ ≫ Chart.spMap π ≫ y (M + 1) = 1 := by
    rw [← Category.assoc, Chart.spMap_comp, haπ, hya]
  obtain ⟨a, ha, hza⟩ := hU _ augQ (M + 1) hkQ (pullback.lift _ (toUnit _) hz) (hext _ _ (by
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hzone]))
  have hM' : RingHom.ker aug ^ (M + 1 + 1) = ⊥ := by
    rw [pow_succ (RingHom.ker aug) (M + 1), hM, Ideal.bot_mul]
  obtain ⟨ψ, ⟨hψa, hψ⟩, -⟩ := hx.2.2 A aug (M + 1) hM' (io ≫ pullback.fst f η[G]) (by
    rw [← Category.assoc, hio, pullback.lift_fst])
  have hz0 : ∀ j, ψ₀ (Chart.zR (M + 1) j) = Chart.zR (M + 1) (0, j) := fun j =>
    (hψ₀ j).trans (toJet_X (M + 1) _)
  have heq : a.comp ψ = π.comp ψ₀ := by
    refine (hx.2.2 _ augQ (M + 1) hkQ (Chart.spMap π ≫ y (M + 1)) hzone).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, ha, hψa]
    · rw [← Chart.spMap_comp, Category.assoc, ← hψ, ← Category.assoc, ← hza, pullback.lift_fst]
    · rw [← AlgHom.comp_assoc, haπ]
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, hz0, Chart.jetAug_zR, Chart.jetAug_zR]
    · rw [hy₀, ← Category.assoc, Chart.spMap_comp]
  let Θ := π.comp (toJetHom k (Fin 1 × Fin d) (M + 1))
  have hΘ : Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ≤
      ((RingHom.ker aug).map a).comap Θ := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have e1 : Θ (MvPowerSeries.X (0, j)) = a (ψ (Chart.zR (M + 1) j)) := by
      have := AlgHom.congr_fun heq (Chart.zR (M + 1) j)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hψ₀] at this
      exact this.symm
    show Θ (MvPowerSeries.X (0, j)) ∈ (RingHom.ker aug).map a
    rw [e1]
    exact Ideal.mem_map_of_mem a ((AlgHom.congr_fun hψa _).trans (Chart.jetAug_zR (M + 1) j))
  intro g hg
  have h2 := Ideal.le_comap_pow _ (M + 1) (Ideal.pow_right_mono hΘ (M + 1) hg)
  rw [← Ideal.map_pow, hM, Ideal.map_bot] at h2
  exact mem_sup_pow_of_toJet_mem_map (M + 1) _ g (Ideal.Quotient.eq_zero_iff_mem.1 h2)
end GlobalTheory.JetSer
