-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.jet_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:05.866017+00:00
-- url     : https://prove2.me/submissions/34158dce-0ad1-4366-80f0-146d8b0f809d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_jet_zero_ext
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_fderiv_eq_of_jetOf
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_cancel_renN
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_jetOf_eq_of_jetPt
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_colsOf_surj
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_fderiv_comp_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_coeff_tay_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnVal.JetUniq
private theorem zero_mem_degLE' {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) :
    (0 : κ →₀ ℕ) ∈ (degLE k : Finset (κ →₀ ℕ)) := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _, ?_⟩, by simp⟩
  ext i
  simp
private theorem jetAug_jetN_zero_eq_apply_zero {n g : ℕ} (F : (Fin n → Fin g → ℂ) → ℂ) :
    (jetAug : Jet ℂ (Fin n × Fin g) 0 →ₐ[ℂ] ℂ) (jetN 0 F) = F 0 := by
  have hcc : ∀ {κ : Type} (R : MvPolynomial κ ℂ),
      MvPolynomial.aeval (fun _ => (0 : ℂ)) R = MvPolynomial.constantCoeff R := by
    intro κ R
    induction R using MvPolynomial.induction_on <;> simp_all
  have hc2 : (MvPolynomial.aeval (fun _ => (0 : ℂ))).comp (MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
      (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ)) =
      MvPolynomial.aeval (fun _ => (0 : ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  change MvPolynomial.aeval (fun _ => (0 : ℂ)) ((MvPolynomial.aeval fun p : Fin 1 × Fin (n * g) =>
      (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ))
      (psTrunc 0 (PullbackSections.tay (fun v => F (colsOf n g v)) 0))) = F 0
  rw [← AlgHom.comp_apply, hc2, hcc]
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq', if_pos (zero_mem_degLE' 0)]
  have e1 := PullbackSections.coeff_tay_zero (fun v => F (colsOf n g v)) 0
  have hf : PullbackSections.fct (0 : Fin 1 × Fin (n * g) →₀ ℕ) = 1 := by simp [PullbackSections.fct]
  have hdir : PullbackSections.dirs (0 : Fin 1 × Fin (n * g) →₀ ℕ) = 0 := by simp [PullbackSections.dirs]
  rw [hf, _root_.one_mul, hdir] at e1
  rw [e1]
  have key : ∀ l : List (Fin (n * g) → ℂ), l = [] →
      iteratedFDeriv ℂ l.length (fun v => F (colsOf n g v)) 0 (fun i => l.get i) = F (colsOf n g 0) := by
    intro l hl
    subst hl
    exact iteratedFDeriv_zero_apply _
  unfold PullbackSections.mD PullbackSections.lD
  exact key _ (by simp)
end GlobalTheory.AnVal.JetUniq
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
namespace GlobalTheory.AnVal.JetUniq
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), Φ.Imm → ∀ (n m : ℕ) (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetMap m ψ Λ → Φ.JetMap m ψ Λ' → ∀ f : (Fin g → ℂ) → ℂ, jetN m (fun w => f (Λ w)) = jetN m (fun w => f (Λ' w)) := by
  intro S A _ _ L x0 g Φ hImm n m ψ Λ Λ' hΛ hΛ' f
  rcases m with _ | k
  · apply jet_zero_ext
    rw [jetAug_jetN_zero_eq_apply_zero, jetAug_jetN_zero_eq_apply_zero]
    simp only [map_zero]
  · have hΛΛ : Λ = Λ' := by
      obtain ⟨hol, hψ⟩ := hΛ
      obtain ⟨hol', hψ'⟩ := hΛ'
      have hpt := cancel_renN n g (k + 1) _ _ (hψ.symm.trans hψ')
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := colsOf_surj n g w
      by_contra hne
      obtain ⟨U, F, hU, hder⟩ := hImm _ (sub_ne_zero.mpr hne)
      have hU0 : (Φ.e 0).left cpt ∈ U := hU trivial
      have hz : Φ.e (Λ (colsOf n g 0)) = Φ.e 0 := by
        rw [show colsOf n g 0 = 0 from rfl, map_zero]
      have hz' : Φ.e (Λ' (colsOf n g 0)) = Φ.e 0 := by
        rw [show colsOf n g 0 = 0 from rfl, map_zero]
      have hjet := jetOf_eq_of_jetPt _ _ hol hol' (k + 1) hpt U
        (by show (Φ.e (Λ (colsOf n g 0))).left cpt ∈ U; rw [hz]; exact hU0)
        (by show (Φ.e (Λ' (colsOf n g 0))).left cpt ∈ U; rw [hz']; exact hU0) F
      have hfd := fderiv_eq_of_jetOf k _ _ hjet
      obtain ⟨hopen, hdiff⟩ := Φ.hol U F
      have hθ : DifferentiableAt ℂ (fun z => valAt' (Φ.e z).left U F) 0 :=
        hdiff.differentiableAt (hopen.mem_nhds hU)
      have h1 := fderiv_comp_lin _ hθ (Λ ∘ₗ colsL n g) v
      have h2 := fderiv_comp_lin _ hθ (Λ' ∘ₗ colsL n g) v
      apply hder
      rw [map_sub, sub_eq_zero]
      exact h1.symm.trans ((congrArg (fun T => T v) hfd).trans h2)
    subst hΛΛ
    rfl
end GlobalTheory.AnVal.JetUniq
