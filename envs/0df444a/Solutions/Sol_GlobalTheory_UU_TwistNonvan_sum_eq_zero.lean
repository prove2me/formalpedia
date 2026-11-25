-- Prove2me | solution 1 for GlobalTheory.UU.TwistNonvan.sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:51.966942+00:00
-- url     : https://prove2.me/submissions/08a0b609-fdc8-4035-86a3-5fccb65462a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffEqZeroOfSumSmulEqZeroOfSeparating
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteExtensionPrimitiveResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfFaithfullyFlatBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsNeZeroIffSvalGenericPointNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistConvNeZero
import Theorems.Thm_GlobalTheory_UU_TwistNonvan_sval_scale
import Theorems.Thm_GlobalTheory_UU_TwistNonvan_sval_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.TwistNonvan
namespace GlobalTheory.UU.TwistNonvan
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm
end GlobalTheory.UU.TwistNonvan
