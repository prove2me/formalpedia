-- Prove2me | solution 1 for GlobalTheory.ChartJet.exists_ptJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:52.608797+00:00
-- url     : https://prove2.me/submissions/8a1add6e-a6d3-4b76-8306-50a63984fa57

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Theorems.Thm_GlobalTheory_ChartJet_exists_pj
import Theorems.Thm_GlobalTheory_ChartJet_jP_zR
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


section
noncomputable section
namespace GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
section Points
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
end Points
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
private theorem jet_spMap_square_comm {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  apply Over.OverMorphism.ext
  simp only [spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp]
  rfl
private theorem jetR_algHom_ext_of_eq_on_zR {κ A : Type} [CommRing A] [Algebra R A] {m : ℕ} (f g : JetR R κ m →ₐ[R] A)
    (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h
variable {x} (hx : IsUnivChart G d x)
include hx
private theorem jetAug_comp_jetTruncR_eq_jetAug_succ (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) := by
  apply jetR_algHom_ext_of_eq_on_zR
  intro j
  rfl
end GlobalTheory.ChartJet
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
variable {x} (hx : IsUnivChart G d x)
include hx
namespace GlobalTheory.ChartJet
theorem _root_.solution (y : ∀ m, sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G) (h₀ : ∀ m, spMap (jetAug R _ m) ≫ y m = 1)
    (h₁ : ∀ m, spMap (jetTruncR R _ m) ≫ y (m + 1) = y m) : ∃ p : Q R d n, ∀ m, ptJ x m p = y m := by
  choose ψ hψ hu using fun m =>
    hx.2.2 (JetR R (Fin n × Fin d) m) (jetAug R _ m) m (ker_jetAug_pow _ m) (y m) (h₀ m)
  have hc : ∀ m, (jetTruncR R (Fin n × Fin d) m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
    intro m
    have hk : RingHom.ker (jetAug R (Fin n × Fin d) m) ^ (m + 1 + 1) = ⊥ :=
      le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans (ker_jetAug_pow _ m).le)
    refine (hx.2.2 (JetR R (Fin n × Fin d) m) (jetAug R _ m) (m + 1) hk (y m) (h₀ m)).unique
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, jetAug_comp_jetTruncR_eq_jetAug_succ hx, (hψ (m + 1)).1]
    · rw [jet_spMap_square_comm, Category.assoc, ← (hψ (m + 1)).2, h₁]
    · rw [← AlgHom.comp_assoc, (hψ m).1, jetAug_comp_jetTruncR_eq_jetAug_succ hx]
    · rw [jet_spMap_square_comm, Category.assoc, hx.1 m, (hψ m).2]
  have hz : ∀ j m, jetTruncR R (Fin n × Fin d) m (ψ (m + 1) (zR (m + 1) j)) = ψ m (zR m j) := by
    intro j m
    exact congrArg (fun φ => φ (zR (m + 1) j)) (hc m)
  choose P hP using fun j => exists_pj (fun m => ψ m (zR m j)) (hz j)
  have hP0 : ∀ j, constantCoeff (P j) = 0 := by
    intro j
    rw [← aug_pj 0, hP j 0]
    show ((jetAug R _ 0).comp (ψ 0)) (zR 0 j) = 0
    rw [(hψ 0).1]
    show (MvPolynomial.aeval fun _ => (0 : R)) (MvPolynomial.X j) = 0
    rw [MvPolynomial.aeval_X]
  refine ⟨⟨P, hP0⟩, fun m => ?_⟩
  have e : jP m ⟨P, hP0⟩ = ψ m := by
    apply jetR_algHom_ext_of_eq_on_zR
    intro j
    rw [jP_zR]
    exact hP j m
  unfold ptJ
  rw [e, (hψ m).2]
end GlobalTheory.ChartJet
