-- Prove2me | solution 1 for GlobalTheory.AnVal.jetRd_mul_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:37:31.148735+00:00
-- url     : https://prove2.me/submissions/df6721d9-948f-4b7b-a7d1-5085914457a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_mul
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_pow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_inv_mul
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_anO_prod
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_prod_ne
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_map_res_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory.AnVal.JetAlg
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AnVal
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → Φ.JetRd m (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' τ τ') (Sum.elim Λ Λ') ∧ Φ.JetRd m φ (fun k => -ε k) (LB.invGen L.L φ ε τ) Λ ∧ ∀ p : ℕ, Φ.JetRd m φ (fun k => (p : ℤ) * ε k) ⟨fun j => τ.s j ^ p⟩ Λ := by
  intro S A _ _ L x0 g Φ n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h1 h2
  refine ⟨⟨fun k => ?_, fun j h => ?_⟩, ⟨h1.1, fun j h => ?_⟩, fun p => ⟨h1.1, fun j h => ?_⟩⟩
  · cases k with
    | inl k => exact h1.1 k
    | inr k => exact h2.1 k
  · have hL : ⊤ ≤ LB.wchart L.L φ (j ∘ Sum.inl) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
    have hR : ⊤ ≤ LB.wchart L.L φ' (j ∘ Sum.inr) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
    unfold LB.mulGen
    rw [Units.val_mul, map_mul, map_res_val, map_res_val]
    refine (congrArg₂ (· * ·) (h1.2 (j ∘ Sum.inl) hL) (h2.2 (j ∘ Sum.inr) hR)).trans ?_
    rw [← map_mul, ← jetN_mul m (anO_prod Φ h1.1 ε hL) (anO_prod Φ h2.1 ε' hR)]
    refine congrArg (toΓ _) (congrArg (jetN m) (funext fun w => ?_))
    rw [Fintype.prod_sum_type]
    rfl
  · have e1 : ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom ((τ.s j)⁻¹).val *
        ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom (τ.s j).val = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1.2 j h] at e1
    have e2 := jetN_inv_mul m (anO_prod Φ h1.1 ε h) (prod_ne Φ h1.1 ε h)
    have hG : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ (-ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k)⁻¹ := by
      funext w
      simp only [zpow_neg, Finset.prod_inv_distrib]
    refine left_inv_eq_right_inv e1 ?_
    rw [mul_comm, ← map_mul]
    beta_reduce
    rw [hG, e2, map_one]
  · have hP : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ((p : ℤ) * ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k) ^ p := by
      funext w
      simp only [mul_comm (p : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]
    beta_reduce
    rw [hP, jetN_pow m (anO_prod Φ h1.1 ε h) p, map_pow, ← h1.2 j h, ← map_pow, ← Units.val_pow_eq_pow_val]
end GlobalTheory.AnVal
