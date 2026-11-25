-- Prove2me | solution 1 for GlobalTheory.UU.ExpLin.expT_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:16.481278+00:00
-- url     : https://prove2.me/submissions/3a5a7e3e-ca2f-47f1-a8ab-4dd4c8294ba0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecComb
import Theorems.Thm_GlobalTheory_UU_ExpLin_sval_secComb
import Theorems.Thm_GlobalTheory_UU_ExpLin_sum_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLin
namespace GlobalTheory.UU.ExpLin
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k n : ℕ) (c : Fin n → Γ(T.left, ⊤)) (σ : Fin n → U.SecGT T k) (f : Fin n → ∀ α, SecBT D T k α), (∀ i, U.ExpT T k (σ i) (f i)) → ∃ (σ' : U.SecGT T k) (f' : ∀ α, SecBT D T k α), U.ExpT T k σ' f' ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ' r z J = ∑ i, gs (r ≫ (fst T G).left) z ⊤ (c i) * sval (σ i) r z J) ∧ ∀ α (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J → sval (f' α) r z J = ∑ i, gs (r ≫ (fst T D.P.A).left) z ⊤ (c i) * sval (f i α) r z J := by
  classical
  intro R _ _ I D A G _ _ U T k n c σ f h
  refine ⟨secComb (fun i => (fst T G).left.appTop.hom (c i)) σ,
    fun α => secComb (fun i => (fst T D.P.A).left.appTop.hom (c i)) (fun i => f i α), fun e => ?_,
    fun Z r z J hJ => sval_secComb _ c σ r z hJ, fun α Z r z J hJ => sval_secComb _ c (fun i => f i α) r z hJ⟩
  choose s hs using fun i => h i e
  refine ⟨Finset.univ.biUnion s, fun Z x rG rB h₁ h₂ h₃ z JG J hG hJ => ⟨fun α hα => ?_, ?_⟩⟩
  · rw [sval_secComb _ c (fun i => f i α) rB z hJ]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1 α
      (fun hi => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)), mul_zero]
  · rw [sval_secComb _ c σ rG z hG]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun α _ =>
      (congrArg (· * _) (sval_secComb (fst T D.P.A).left c (fun i => f i α) rB z hJ)).symm)
    rw [h₃]
    exact sum_comb _ _ _ s (fun i α => sval (f i α) rB z J) _
      (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1) (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).2)
end GlobalTheory.UU.ExpLin
