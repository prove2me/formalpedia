-- Prove2me | solution 1 for GlobalTheory.FamDim.exists_term_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:56:21.360204+00:00
-- url     : https://prove2.me/submissions/2beb7e6a-7b0e-421e-b789-49eb1d19fd96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTermBasis
import Theorems.Thm_P2M_GlobalTheory_FamDim_fam__eq_ad54a1696e5f
import Theorems.Thm_GlobalTheory_T_exists_twist_basis_off_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamDim
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
  [Algebra (FractionRing R) F] {k : ℕ}
namespace GlobalTheory.FamDim
theorem _root_.solution (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hT : TwistBaseChangeStatement)
    [IsNoetherianRing R]
    (hW : ∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W))
    (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
        ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, resTop _ (gF D F (c i)) * (b i).f j := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have key : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), t = Spec.map (CommRingCat.ofHom f) →
      ∀ φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left),
        φ = (fun i => (snd (Over.mk t) D.P.A).left ≫ DegPre.famφB D α i) →
      ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L φ (DegPre.famε k)),
        IsSecBasis (T := Over.mk t) (A := D.P.A) _ b := by
    rintro t rfl φ rfl
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_twist_basis_off_prime hP hG hT R D hW ⊥ k hk α
    refine ⟨fun i => pullSec D.P.L (DegPre.famφB D α) (DegPre.famε k) (b i) _, hb F f (fun s hs => ?_) _
      (fun i j => rfl)⟩
    refine IsUnit.mk0 _ fun h0 => hs ?_
    have h1 : algebraMap R (FractionRing R) s = 0 := (algebraMap (FractionRing R) F).injective (h0.trans (map_zero _).symm)
    exact (IsFractionRing.to_map_eq_zero_iff (K := FractionRing R)).1 h1
  obtain ⟨b, hb⟩ := key (jFK (R := R) F ≫ jK R) (by
    simp only [jFK, jK, f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) _ (famφ_eq α)
  refine ⟨b, fun s => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb s
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨fun i => e (r i), fun j => (hr j).trans (Finset.sum_congr rfl fun i _ => ?_), fun c hc => ?_⟩
  · congr 2
    show _ = (fst (TF (R := R) F) D.P.A).left.appTop.hom (e.symm (e (r i)))
    rw [e.symm_apply_apply]
  · have := hu (fun i => e.symm (c i)) hc
    funext i
    rw [← this]
    exact (e.apply_symm_apply _).symm
end GlobalTheory.FamDim
