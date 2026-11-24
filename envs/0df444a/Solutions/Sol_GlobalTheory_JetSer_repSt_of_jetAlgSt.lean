-- Prove2me | solution 1 for GlobalTheory.JetSer.repSt_of_jetAlgSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:46.988977+00:00
-- url     : https://prove2.me/submissions/3f30f76d-3605-4945-85aa-959dcd320807

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Theorems.Thm_GlobalTheory_JetSer_rep_jetAug_comp_trunc
import Theorems.Thm_GlobalTheory_JetSer_isFPt_of_isUnivChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]
namespace GlobalTheory.JetSer
theorem _root_.solution (hJ : JetAlgSt) : RepSt := by
  intro R _ G _ d x hx κ _
  obtain ⟨hτ, htr, hinj, hsur, hsub⟩ := hJ R κ
  have hxa := (isFPt_of_isUnivChart hx).2
  have haug : ∀ (a : Fin d → MvPowerSeries κ R), (∀ j, constantCoeff (a j) = 0) → ∀ m
      (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m), (∀ j, ψ (zR m j) = toJet m (a j)) →
      (jetAug R κ m).comp ψ = jetAug R (Fin d) m := by
    intro a ha m ψ hψ
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, hψ, (htr m _).2, ha, jetAug_zR]
  have hfp : ∀ a (y : Fam G κ), Rep x a y → IsFPt y := by
    rintro a y ⟨ha, hy⟩
    choose ψ hψ hy using hy
    refine ⟨fun m => ?_, fun m => ?_⟩
    · have e : (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
        refine jet_ext fun j => ?_
        rw [AlgHom.comp_apply, hψ, (htr m _).1]
        exact (hψ m j).symm
      rw [hy, hy, ← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hx.1]
    · rw [hy, ← Category.assoc, spMap_comp, haug a ha m _ (hψ m), hxa]
  refine ⟨fun a ha => ?_, fun y hy => ?_, hfp, ⟨fun j => by simp, fun m => ?_⟩, ?_⟩
  · choose ψ hψ using fun m => (hsub (Fin d) a ha m).1
    refine ⟨fun m => spMap (ψ m) ≫ x m, ⟨ha, fun m => ⟨ψ m, hψ m, rfl⟩⟩, ?_⟩
    rintro y ⟨-, hy⟩
    funext m
    obtain ⟨ψ', h1, h2⟩ := hy m
    have : ψ' = ψ m := jet_ext fun j => (h1 j).trans (hψ m j).symm
    rw [h2, this]
  · have hU := fun m => hx.2.2 (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) (y m) (hy.2 m)
    choose ψ hψ hu using hU
    have hc : ∀ m, (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
      intro m
      have hk : RingHom.ker (jetAug R κ m) ^ (m + 1 + 1) = ⊥ := by
        rw [pow_succ (RingHom.ker (jetAug R κ m)) (m + 1), ker_jetAug_pow, Ideal.bot_mul]
      refine (hx.2.2 (JetR R κ m) (jetAug R κ m) (m + 1) hk (y m) (hy.2 m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [← AlgHom.comp_assoc, rep_jetAug_comp_trunc, (hψ (m + 1)).1]
      · rw [← spMap_comp, Category.assoc, ← (hψ (m + 1)).2, hy.1 m]
      · rw [← AlgHom.comp_assoc, (hψ m).1, rep_jetAug_comp_trunc]
      · rw [← spMap_comp, Category.assoc, hx.1 m, ← (hψ m).2]
    have hex : ∀ j, ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = ψ m (zR m j) := fun j =>
      hsur (fun m => ψ m (zR m j)) (fun m => AlgHom.congr_fun (hc m) (zR (m + 1) j))
    choose a ha using hex
    refine ⟨a, ⟨fun j => ?_, fun m => ⟨ψ m, fun j => (ha j m).symm, (hψ m).2⟩⟩, ?_⟩
    · rw [← (htr 0 _).2, ha, ← jetAug_zR (R := R) 0 j]
      exact AlgHom.congr_fun (hψ 0).1 _
    · rintro a' ⟨ha', hy'⟩
      funext j
      refine hinj _ _ fun m => ?_
      obtain ⟨ψ', h1, h2⟩ := hy' m
      rw [ha, ← h1, hu m ψ' ⟨haug a' ha' m ψ' h1, h2⟩]
  · refine ⟨(Algebra.ofId R _).comp (jetAug R (Fin d) m), fun j => ?_, ?_⟩
    · obtain ⟨τ, h, -⟩ := hτ m
      rw [AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, ← h, map_zero]
    · rw [← spMap_comp, Category.assoc, hxa]
      exact (MonObj.comp_one _).symm
  · rintro κ' _ b ψ hb hψ a y ⟨ha, hy⟩
    obtain ⟨-, htr', -, -, hsub'⟩ := hJ R κ'
    have hs := fun m => (hsub' κ b hb m).2 (ψ m) (hψ m)
    refine ⟨fun j => ?_, fun m => ?_⟩
    · have e : (jetAug R κ' 0).comp (ψ 0) = jetAug R κ 0 := by
        refine jet_ext fun i => ?_
        rw [AlgHom.comp_apply, hψ, (htr' 0 _).2, hb, jetAug_zR]
      rw [← (htr' 0 _).2, ← hs, ← ha j, ← (htr 0 _).2]
      exact AlgHom.congr_fun e _
    · obtain ⟨φ, h1, h2⟩ := hy m
      refine ⟨(ψ m).comp φ, fun j => ?_, ?_⟩
      · rw [AlgHom.comp_apply, h1, hs]
      · show spMap (ψ m) ≫ y m = _
        rw [h2, ← Category.assoc, spMap_comp]
end GlobalTheory.JetSer
