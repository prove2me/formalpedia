-- Prove2me | solution 1 for GlobalTheory.SS.OrdMono.ord_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:05.089794+00:00
-- url     : https://prove2.me/submissions/d473a1fd-0281-421d-a8a5-545c1c3c82c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel
import Theorems.Thm_GlobalTheory_SS_OrdMono_chain_model
import Theorems.Thm_GlobalTheory_SS_OrdMono_isUnit_cstK
import Theorems.Thm_GlobalTheory_SS_OrdMono_chart
import Theorems.Thm_GlobalTheory_SS_OrdMono_extends_res
import Theorems.Thm_GlobalTheory_SS_OrdMono_exists_pull
import Theorems.Thm_GlobalTheory_SS_Ord_exists_etale_coord
import Theorems.Thm_GlobalTheory_SS_Ord_isOpenImmersion_of_extends_id_of_etale
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_injective
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_not_isUnit_cst
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cstK
import Theorems.Thm_GlobalTheory_SS_Ord_rs_jac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdMono
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdMono
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [IsIntegral A.left] (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ (M N : Model R A) (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D π n → (∃ y ∈ M.sp, DefAt M N (𝟙 A) y) → m ≤ n ∧ (m = n → GenIso M N (𝟙 A)) := by
  intro R K _ _ _ _ _ _ π hπ A _ I _ _ D hD M N m n hM hN hm hn ⟨y, hy, U, g, hyU, hg⟩
  have hx : g ⟨y, hyU⟩ ∈ N.sp := by
    have : (g ≫ N.Y.hom) ⟨y, hyU⟩ = (U.ι ≫ M.Y.hom) ⟨y, hyU⟩ := by rw [hg.1]
    exact this.trans hy
  obtain ⟨V, t, hV, hxV, -, ht⟩ := GlobalTheory.SS.Ord.exists_etale_coord R K A I hD.1 N (g ⟨y, hyU⟩) ⊤ trivial
  obtain ⟨s, hs, e⟩ := chart hπ N hN hD hn hV ⟨_, hxV, hx⟩ ht
  obtain ⟨W, r, hW, hyW, hle, hr⟩ := GlobalTheory.SS.Ord.exists_etale_coord R K A I hD.1 M y (U.ι ''ᵁ g ⁻¹ᵁ V) ⟨⟨y, hyU⟩, hxV, rfl⟩
  have hWU : W ≤ U := hle.trans (U.ι_image_le _)
  have hg' := extends_res hg hWU
  have htop : ⊤ ≤ (M.Y.left.homOfLE hWU ≫ g) ⁻¹ᵁ V := by
    intro z _
    obtain ⟨w, hw, e⟩ := hle z.2
    have : M.Y.left.homOfLE hWU z = w := Subtype.ext (by rw [Scheme.homOfLE_apply]; exact e.symm)
    show g (M.Y.left.homOfLE hWU z) ∈ V
    rw [this]; exact hw
  obtain ⟨ψ, hj, hc, hψ, het⟩ := exists_pull hg' V htop
  have key : jm M D W (fun i => ψ (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app W).hom (ψ s) := by
    have := congrArg (rs _ hj) e
    rw [jm, rs_jac, map_mul, rs_cstK, ← hψ] at this
    simpa only [jm, hψ] using this
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  refine ⟨not_lt.1 fun hlt => ?_, ?_⟩
  · obtain ⟨s', e'⟩ := hm.1 W fun i => ψ (t i)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = n + (k + 1 : ℕ) := ⟨(m - n - 1).toNat, by omega⟩
    replace e' := key.symm.trans e'
    rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cst, ← map_mul] at e'
    have h1 := j_app_injective M W ((isUnit_cstK hπ _ n).mul_left_cancel e')
    have h2 := hs.map ψ
    rw [h1, pow_succ, map_mul] at h2
    exact not_isUnit_cst M W ⟨y, hyW, hy⟩ hπ.not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h2))
  · rintro rfl
    obtain ⟨s', e'⟩ := hm.1 W r
    obtain ⟨a, ha, hb⟩ := chain_model M D W r (fun i => ψ (t i)) hr
    rw [key, jm, e', mul_left_comm, ← map_mul] at ha
    have h1 := j_app_injective M W ((isUnit_cstK hπ _ m).mul_left_cancel ha)
    have h2 := hb (isUnit_of_mul_isUnit_left (show IsUnit (_ * _) from h1.subst (hs.map ψ)))
    have h3 : (ψ.comp (MvPolynomial.eval₂Hom (cst N V) t)).Etale := by
      rw [MvPolynomial.comp_eval₂Hom, hc]; exact h2
    have h4 : ψ.Etale := by
      algebraize [MvPolynomial.eval₂Hom (cst N V) t, ψ, ψ.comp (MvPolynomial.eval₂Hom (cst N V) t)]
      exact Algebra.Etale.of_restrictScalars (R := MvPolynomial I R) _ _
    exact ⟨y, hy, W, _, hyW, hg', GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale R K A M N W _ hg' (het hW hV h4)⟩
end GlobalTheory.SS.OrdMono
