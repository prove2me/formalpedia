-- Prove2me | solution 1 for GlobalTheory.UU.ExpLinC.expF_lincomb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:42.912203+00:00
-- url     : https://prove2.me/submissions/7fc55292-895e-41d1-9b4a-9efe0260c0ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalLincomb
import Theorems.Thm_GlobalTheory_UU_ExpLinC_sval_lincomb
import Theorems.Thm_GlobalTheory_UU_ExpLin_gs_scal_mul
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLinC
namespace GlobalTheory.UU.ExpLinC
theorem _root_.solution : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s : Fin n → Raw D F k) (t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s' : Raw D F k), (∀ i, U.ExpF F k (t i) (s i)) → (∀ j, t'.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (t i).f j) → (∀ α j, (s' α).f j = ∑ i, DegPre.constBF D F (c i) _ * (s i α).f j) → U.ExpF F k t' s') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k n c t s t' s' H ht hs
  choose m a σ f h1 h2 h3 using H
  let e : Fin (Fintype.card (Σ i, Fin (m i))) ≃ (Σ i, Fin (m i)) := (Fintype.equivFin _).symm
  refine ⟨_, fun p => c (e p).1 * a (e p).1 (e p).2, fun p => σ (e p).1 (e p).2, fun p => f (e p).1 (e p).2,
    fun p => h1 _ _, fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e0 z J hJ => ?_⟩
  · rw [e.sum_comp (fun q => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left (c q.1 * a q.1 q.2)) *
      sval (σ q.1 q.2) rG z JG), Fintype.sum_sigma,
      sval_lincomb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (fun i => scal (fst (TFK (R := V) F) A.A).left (c i)) ht rA z hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 i Z rA y rG e1 e2 z JA JG hA hG]
    ring
  · rw [e.sum_comp (fun q => gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left (c q.1 * a q.1 q.2)) *
      sval (f q.1 q.2 α) rB z J), Fintype.sum_sigma]
    refine (sval_lincomb (fun i => scal (fst (TF (R := V) F) D.P.A).left (c i)) (hs α) rF z hJ).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 i α Z rF rB e0 z J hJ]
end GlobalTheory.UU.ExpLinC
