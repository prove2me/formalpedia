-- Prove2me | solution 1 for GlobalTheory.per_bor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:16.742082+00:00
-- url     : https://prove2.me/submissions/fba4d23e-04ce-4e89-8328-c669f70decde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TriangularFrameMovesPeriodBlockTriangular
import Theorems.Thm_GlobalTheory_PerBor_inv_support
import Theorems.Thm_GlobalTheory_PerBor_det_of_support
import Theorems.Thm_GlobalTheory_PerBor_inv_diag
import Theorems.Thm_GlobalTheory_PerBor_moveMat_diag
import Theorems.Thm_GlobalTheory_PerBor_moveMat_support
import Theorems.Thm_GlobalTheory_PerBor_moveMat_mulVec
import Theorems.Thm_GlobalTheory_PerMove_bor_diag_ne
import Theorems.Thm_GlobalTheory_Relab_relab_good
import Theorems.Thm_GlobalTheory_T_cmType_letter_frame_column_dictionary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ a, Pf (rmul x b) a = h₀ *ᵥ Pf x a) ∧ (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ ‖h₀.det‖ = ∏ j, ‖h₀ j j‖ ∧ ((∀ τ i, ‖b τ i i‖ = 1) → ‖h₀.det‖ = 1) ∧ ∀ (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : ℂ), Even n → t₀ ^ 2 * h₀.det = 1 → (∏ j, h₀⁻¹ j j ^ a ((e j).1, (e j).2)) * t₀ ^ n = bchar (laU (unfOf e F M un) a n k) b := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx b hb
  obtain ⟨⟨idx, hty, hcol, hper⟩, hp0, -⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  have hq : (F.Di k).q = Dw.q := hp0.symm.trans (hB.type k).1
  have hlt : ∀ j, ((idx j).2 : ℕ) < (F.Di k).q → ((e j).2 : ℕ) < (F.Di k).q := by
    intro j hj
    have h1 := hty j
    rw [if_pos hj] at h1
    have h2 := ((M.X k).cmType _).1 (idx j).1.2
    rw [← h1, (hB.type k).2, hrt] at h2
    have h3 : Dw.mult (e j).1 = Dw.q := if_neg h2
    have := (e j).2.isLt
    omega
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (F.Di k).q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have c1 := hcol j
    have c2 := hcol j'
    have l1 := hlt j
    have l2 := hlt j'
    have t1 := hty j
    have t2 := hty j'
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at h2 c1 t1
      have hj' : ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_pos hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      have := l1 hj
      have := l2 hj'
      omega
    · rw [if_neg hj] at h2 c1 t1
      have hj' : ¬ ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_neg hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      omega
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (F.Di k).q idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (F.Di k).q idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (F.Di k).q idx b, hu, fun a => ?_, PerBor.inv_support _ _ _ hu hs,
    by rw [hdet, norm_prod], fun h1 => ?_, fun un a n t₀ hn ht => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (M.X k).Gm x (M.φ k a : Fin r → E) _ _
      (fun j => by rw [hPf, hper]) (fun j => by rw [hPf, hper])
  · rw [hdet, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact h1 _ _
    · rw [norm_inv, h1, inv_one]
  · obtain ⟨m, rfl⟩ := hn
    have ht2 : t₀ ^ 2 = ∏ j, (PerBor.moveMat (F.Di k).q idx b j j)⁻¹ := by
      rw [Finset.prod_inv_distrib, ← hdet]
      exact eq_inv_of_mul_eq_one_left ht
    rw [← two_mul, pow_mul, ht2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (M.X k).Ψ) (i : Fin r) => b τ i i ^ laU (unfOf e F M un) a (2 * m) k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, ← pow_add, hdiag]
    have hm' : 2 * m / 2 = m := by omega
    have hp : ((unfOf e F M un).X k).p0 = (F.Di k).q := hp0
    have c1 := hcol j
    have t1 := hty j
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rw [hp, hm']
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at c1 t1
      have := hlt j hj
      have t2 : conjEmb (idx j).1.1 = relab c σ (e j).1 := t1.symm
      rw [if_pos hj, if_neg (by omega), t2, hinv,
        show (F.Di k).q - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    · rw [if_neg hj] at c1 t1
      rw [if_neg hj, if_pos (by omega), ← t1, hinv,
        show ((idx j).2 : ℕ) - (F.Di k).q = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
end GlobalTheory
