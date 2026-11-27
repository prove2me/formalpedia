-- Prove2me | solution 1 for GlobalTheory.AnValJetGlob.jetRd_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:48:51.400866+00:00
-- url     : https://prove2.me/submissions/983a5078-cd25-4190-a358-ec15668c5454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Theorems.Thm_GlobalTheory_AnValJetGlob_appLE_spMap_jetPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolFam_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnValJetGlob
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AnValJetGlob
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (q : (Fin (n * g) → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q), (∀ v, Φ.GenRd φ ε t (q v) (fun k => Λ k (colsOf n g v)) 1) → Φ.JetRd m (fun k => (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m) ≫ φ k) ε (LB.pullGen L.L φ ε t (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m)) Λ := by
  intro S A _ _ L x0 g Φ n m Z K _ φ ε t Λ q hq H
  refine ⟨fun k => ?_, fun j h => ?_⟩
  · have he : ∀ v, q v ≫ φ k = (Φ.e (Λ k (colsOf n g v))).left := fun v => (H v).1 k
    have hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ k (colsOf n g v))).left) := by
      have h := isHolFam_comp q hq (φ k)
      rwa [show (fun v => q v ≫ φ k) = fun v => (Φ.e (Λ k (colsOf n g v))).left from funext he] at h
    refine ⟨hol, ?_⟩
    beta_reduce
    rw [Category.assoc, jetPt_comp q hq (φ k) _ hol he]
  · have : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) :=
      isLocalHom_jetMap (K := ℂ) (m := m) _ _
    have h' : ⊤ ≤ (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt q hq m) ⁻¹ᵁ LB.wchart L.L φ j := by
      intro x hx
      have hx' := h hx
      simp only [LB.wchart] at hx' ⊢
      exact Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx' k
        simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using this
    obtain ⟨hU, hf⟩ := appLE_spMap_jetPt q hq _ _ h'
    have hj : jetOf m (fun v => valAt' (q v) (LB.wchart L.L φ j) (t.s j).val) =
        jetOf m (fun v => ∏ k, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) := by
      refine jetOf_congr m ((eventually_mem q hq hU).mono fun v hv => ?_)
      have := (H v).2 j hv
      rw [_root_.one_mul] at this
      exact this
    have hf' := hf (t.s j).val
    rw [hj] at hf'
    refine Eq.trans ?_ hf'
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    show ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom
      (((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE _).op).hom _) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
end GlobalTheory.AnValJetGlob
