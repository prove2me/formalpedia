-- Prove2me | solution 1 for GlobalTheory.PowChange.exists_block_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:47.755454+00:00
-- url     : https://prove2.me/submissions/bbb0ae5b-d0f3-4917-8380-0e18138c65be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NonzeroLocusConstMul
import Theorems.Thm_GlobalTheory_PowChange_sc_zero_comp
import Theorems.Thm_GlobalTheory_PowLie_isLieBasis_pow
import Theorems.Thm_GlobalTheory_PowLie_isLieComb_iff_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowChange
open GlobalTheory.PowLie
variable {R : Type} [CommRing R]
namespace GlobalTheory.PowChange
theorem _root_.solution {G' G : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {j g n : ℕ} (p : Out.IsPowGrp G' G j) (hg : j * g = n) {v v' : Fin g → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') (M : Matrix (Fin g) (Fin g) R)
    (hM : ∀ i, IsLieComb (M i) v (v' i)) (u : Fin n → (epsR R ⟶ G'))
    (hu : ∀ (i i' : Fin j) (k : Fin g),
      u ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v k else 1) :
    ∃ (w : Fin n → (epsR R ⟶ G')) (M' : Matrix (Fin n) (Fin n) R), IsLieBasis w ∧
      (∀ (i i' : Fin j) (k : Fin g),
        w ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v' k else 1) ∧
      (∀ i, IsLieComb (M' i) u (w i)) ∧ M'.det = M.det ^ j := by
  subst hg
  obtain ⟨w, hw, hw'⟩ := isLieBasis_pow R G' G j g p v' hv'
  let e : Fin g × Fin j ≃ Fin (j * g) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [isLieComb_iff_prod]
    refine p.lim.hom_ext fun ⟨i'⟩ => ?_
    have := p.hom i'
    change _ ≫ p.pr i' = _ ≫ p.pr i'
    refine Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm
    have hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 :=
      fun i k => hu i i' k
    rw [hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']
    · have h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R))
          (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k))
            (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) =
          sc (if i = i' then M k k' else 0) ≫ v k' := fun k' => by
        change (sc _ ≫ u _) ≫ p.pr i' = _
        rw [Category.assoc, hu', if_pos rfl]
        congr 2
        simp [e, Matrix.blockDiagonal_apply]
      rw [Finset.prod_congr rfl fun k' _ => h₁ k']
      split_ifs with h
      · exact (isLieComb_iff_prod _ _ _).1 (hM k)
      · exact (Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm
    · intro i'' _ hi
      refine Finset.prod_eq_one fun k' _ => ?_
      change (sc _ ≫ u _) ≫ p.pr i' = _
      rw [Category.assoc, hu', if_neg hi, comp_one]
    · simp
  · rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    simp
end GlobalTheory.PowChange
