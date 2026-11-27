-- Prove2me | solution 1 for GlobalTheory.AnValGenCorr.genRd_corr_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:22.204406+00:00
-- url     : https://prove2.me/submissions/54fa35ad-d047-46b9-8426-7fdc2ce9a1d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Theorems.Thm_GlobalTheory_AnValGenCorr_chart_iff
import Theorems.Thm_GlobalTheory_AnValGenCorr_exists_chart
import Theorems.Thm_GlobalTheory_AnValGenCorr_corr_val
import Theorems.Thm_GlobalTheory_AnValGenCorr_val_inv
import Theorems.Thm_GlobalTheory_AnValGenCorr_prod_fibre
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_res


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
open GlobalTheory GlobalTheory.AnValGenCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValGenCorr
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  classical
  intro S A _ _ L x0 g Φ Z K K' _ _ φ ε φ' ε' t t' q p p' v v' h h'
  have hA : LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι,
      (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧
      v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k := by
    intro hc
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart L.L L.isLB (q ≫ ψ)
    refine ⟨J, hJ, ?_⟩
    have e := corr_val L.L φ ε φ' ε' t t' hc J q hJ
    have e1 := h.2 (fun k => J (φ k)) ((chart_iff L.L φ _ q).2 fun k => hJ _)
    have e2 := h'.2 (fun k => J (φ' k)) ((chart_iff L.L φ' _ q).2 fun k => hJ _)
    exact e1.symm.trans (e.trans e2)
  refine ⟨hA, ?_, ⟨?_, ?_⟩, ⟨h.1, ?_⟩⟩
  · rintro hc hs ⟨π, hπ, hπ'⟩
    obtain ⟨J, hJ, e⟩ := hA hc
    have n1 : ∀ k, Φ.fr (J (φ k)) (π (φ k)) ≠ 0 := fun k => by
      rw [← hπ k]; apply Φ.fr_ne; rw [← h.1 k]; exact hJ _
    have n2 : ∀ k, Φ.fr (J (φ' k)) (π (φ' k)) ≠ 0 := fun k => by
      rw [← hπ' k]; apply Φ.fr_ne; rw [← h'.1 k]; exact hJ _
    let s : Finset (Z ⟶ A.left) := Finset.univ.image φ ∪ Finset.univ.image φ'
    have hf : ∀ ψ ∈ s, Φ.fr (J ψ) (π ψ) ≠ 0 := by
      intro ψ hψ
      rcases Finset.mem_union.1 hψ with hψ | hψ
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n1 k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n2 k
    have p1 := prod_fibre φ ε (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p2 := prod_fibre φ' ε' (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p3 : ∏ k, Φ.fr (J (φ k)) (π (φ k)) ^ ε k = ∏ k, Φ.fr (J (φ' k)) (π (φ' k)) ^ ε' k := by
      refine p1.trans (Eq.trans ?_ p2.symm)
      refine Finset.prod_congr rfl fun ψ _ => ?_
      congr 1
      exact hs ψ
    simp only [hπ, hπ'] at e
    rw [p3] at e
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n2 k)) e
  · rintro (k | k)
    · exact h.1 k
    · exact h'.1 k
  · intro j hj
    have hj0 := (chart_iff L.L _ j q).1 hj
    have e1 := h.2 (j ∘ Sum.inl) ((chart_iff L.L φ _ q).2 fun k => hj0 (Sum.inl k))
    have e2 := h'.2 (j ∘ Sum.inr) ((chart_iff L.L φ' _ q).2 fun k => hj0 (Sum.inr k))
    refine (ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul q _ _ _).trans ?_
    refine (congrArg₂ (· * ·) ((vtf_val_res q _ hj _).trans e1) ((vtf_val_res q _ hj _).trans e2)).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  · intro j hj
    have e1 := h.2 j hj
    have e2 := val_inv q hj (t.s j)
    refine e2.trans ?_
    refine (congrArg (·⁻¹) e1).trans ?_
    simp only [mul_inv, zpow_neg, Finset.prod_inv_distrib]
end GlobalTheory.AnValGenCorr
