-- Prove2me | solution 1 for GlobalTheory.JetSer.exUnique_ser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:52.037791+00:00
-- url     : https://prove2.me/submissions/407f3b2b-3627-4ee3-9c60-2705b2a52e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExUniqueSer
import Theorems.Thm_GlobalTheory_JetSer_IsFPt_zero_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution (hJ : JetAlgSt) (hR : RepSt) (hS : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {k : ℕ} {Y : Over (Spec (CommRingCat.of R))}
    (L : ∀ T : Over (Spec (CommRingCat.of R)), (Fin k → (T ⟶ G)) → (T ⟶ Y))
    (hL : ∀ (T T' : Over (Spec (CommRingCat.of R))) (h : T' ⟶ T) (y : Fin k → (T ⟶ G)),
      h ≫ L T y = L T' (fun j => h ≫ y j))
    (U : Y.left.Opens) (hU : ⊤ ≤ (L _ (fun _ => η[G])).left ⁻¹ᵁ U) (f : Γ(Y.left, U)) :
    ∃! g : PS R k d, ∀ (n : ℕ) (a : Fin k → Pt R n d) (y : Fin k → Fam G (Fin n × Fin d)),
      (∀ j, Rep x (a j) (y j)) → HasSer (fun m => (L _ (fun j => y j m)).left) U f (ev a g) := by
  obtain ⟨h1, -, h3, -, h5⟩ := hR R G d x hx (Fin k × Fin d)
  have hpt : ∀ (j : Fin k) (i : Fin d), constantCoeff (pt R (n := k) d j i) = 0 :=
    fun j => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt j
  choose y₀ hy₀ using fun j : Fin k => (h1 (pt R (n := k) d j) (hpt j)).exists
  have hF : ∀ j, IsFPt (y₀ j) := fun j => h3 _ _ (hy₀ j)
  have hcomp : ∀ m, (spMap (jetTruncR R (Fin k × Fin d) m)).left ≫ (L _ (fun j => y₀ j (m + 1))).left =
      (L _ (fun j => y₀ j m)).left := by
    intro m
    rw [← Over.comp_left, hL]
    congr 2
    funext j
    exact (hF j).1 m
  have h0 : ⊤ ≤ (L _ (fun j => y₀ j 0)).left ⁻¹ᵁ U := by
    have e : L _ (fun j => y₀ j 0) = toUnit _ ≫ L _ (fun _ => η[G]) := by
      rw [hL]
      congr 1
      funext j
      exact (hF j).zero_eq_one
    rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
    intro p _
    exact hU (Set.mem_univ _)
  obtain ⟨⟨τ, hτ⟩, -, -, hsub⟩ :=
    hS R (Fin k × Fin d) Y.left (fun m => (L _ (fun j => y₀ j m)).left) hcomp U h0
  refine ⟨τ f, fun n a y hy => ?_, fun g hg => ?_⟩
  · let b : Fin k × Fin d → MvPowerSeries (Fin n × Fin d) R := fun p => a p.1 p.2
    have hb : ∀ p, constantCoeff (b p) = 0 := fun p => (hy p.1).1 p.2
    choose ψ hψ using fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin k × Fin d) b hb m).1
    have hyy : ∀ j, y j = fun m => spMap (ψ m) ≫ y₀ j m := by
      intro j
      have r := h5 (Fin n × Fin d) b ψ hb hψ _ _ (hy₀ j)
      have e : (fun i => MvPowerSeries.subst b (pt R (n := k) d j i)) = a j := by
        funext i
        exact MvPowerSeries.subst_X (hasSubst_of_constantCoeff_zero hb) (j, i)
      rw [e] at r
      exact ((hR R G d x hx (Fin n × Fin d)).1 (a j) (hy j).1).unique (hy j) r
    have r := hsub (Fin n × Fin d) b ψ hb hψ f (τ f) ((hτ f _).2 rfl)
    have e : (fun m => (L _ (fun j => y j m)).left) =
        fun m => (spMap (ψ m)).left ≫ (L _ (fun j => y₀ j m)).left := by
      funext m
      rw [← Over.comp_left, hL]
      simp only [hyy]
    rw [e]
    exact r
  · have r := hg k (fun j => pt R (n := k) d j) y₀ hy₀
    have e : ev (fun j => pt R (n := k) d j) g = g := by
      unfold ev
      exact congrFun MvPowerSeries.subst_self g
    rw [e] at r
    exact (hτ f g).1 r
end GlobalTheory.JetSer
