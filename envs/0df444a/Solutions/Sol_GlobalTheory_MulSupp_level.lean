-- Prove2me | solution 1 for GlobalTheory.MulSupp.level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:53.161874+00:00
-- url     : https://prove2.me/submissions/fe24bb09-9232-4f5f-9598-3b64a814d40f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProductSupportInSubgroupTheta
import Theorems.Thm_GlobalTheory_MulSupp_sval_eq_zero
import Theorems.Thm_GlobalTheory_MulSupp_exists_sub_sum
import Theorems.Thm_GlobalTheory_MulSupp_exists_prod
import Theorems.Thm_GlobalTheory_MulSupp_val_coord_mul
import Theorems.Thm_GlobalTheory_sval_eq_zero_of_sum_mul_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory GlobalTheory.MulSupp
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.MulSupp
theorem _root_.solution {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G) (Λ : AddSubgroup D.X) (k l : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) (f) (f') (f'')
    (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) l σ' f') (h'' : U.ExpT (𝟙_ _) (k + l) σ'' f'')
    (hm : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J →
      sval σ'' r z J = sval σ r z J * sval σ' r z J)
    (hf : ∀ α ∉ Λ, ∀ j, (f α).f j = 0) (hf' : ∀ α ∉ Λ, ∀ j, (f' α).f j = 0) (χ₀ : D.X) (hχ : χ₀ ∉ Λ) (e : ℕ)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f'' χ₀) r z J = 0 := by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  obtain ⟨s'', hs''⟩ := h'' e
  have c₁ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left),
      (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (snd (𝟙_ _) G).left = x ≫ (fstG I e G).left := fun Z x =>
    (Category.assoc _ _ _).trans (congrArg (fun q => x ≫ q.left) (lift_snd (toUnit _) (fstG I e G)))
  have c₂ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left →
      r ≫ (fst (𝟙_ _) D.P.A).left = (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (fst (𝟙_ _) G).left := by
    intro Z x r hr
    have a₁ : fst (𝟙_ _) D.P.A = snd _ D.P.A ≫ toUnit _ := toUnit_unique _ _
    have a₂ : (U.gt e).pG ≫ toUnit _ = lift (toUnit _) (fstG I e G) ≫ fst (𝟙_ _) G := toUnit_unique _ _
    rw [a₁, Over.comp_left, ← Category.assoc, hr]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => x ≫ q.left) a₂).trans (Category.assoc _ _ _).symm)
  have ex : ∀ (g : D.X) (p : D.X × D.X), ∃ q : SecBT D (𝟙_ _) (k + l) g,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval q r z J = if p.1 + p.2 = g then
        sval (f p.1) r z J * sval (f' p.2) r z J * (cubAt D p.1 p.2 (r ≫ (snd _ D.P.A).left) z J).val else 0 := by
    intro g p
    by_cases hp : p.1 + p.2 = g
    · subst hp
      simpa only [if_true] using exists_prod D (𝟙_ _) k l p.1 p.2 (f p.1) (f' p.2)
    · exact ⟨H1.SectionArithmetic.secZero _, fun Z r z J hJ => by rw [if_neg hp]; exact sval_eq_zero _ (fun _ => rfl) r z hJ⟩
  choose q hq using ex
  choose d hd using fun g => exists_sub_sum (f'' g) (q g) (s ×ˢ s')
  let S : Finset D.X := s'' ∪ (s ×ˢ s').image (fun p => p.1 + p.2)
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  by_cases hS : χ₀ ∈ S
  swap
  · exact (hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ).1 χ₀ fun h => hS (Finset.mem_union_left _ h)
  have H := sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) (Fin 4) (famφT D (𝟙_ _))
    (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
      obtain ⟨-, E⟩ := hs Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨-, E'⟩ := hs' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨E₀, E''⟩ := hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      rw [hm _ _ z JG hJG, pow_add, _root_.mul_mul_mul_comm, E, E', Finset.sum_mul_sum, ← Finset.sum_product'] at E''
      simp only [hd _ Z r z J hJ, hq _ _ Z r z J hJ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [sub_eq_zero, ← Finset.sum_subset Finset.subset_union_left (fun g _ hg => by rw [E₀ g hg, zero_mul]), ← E'',
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : D.X × D.X => p.1 + p.2) hp)), hr,
        _root_.mul_mul_mul_comm, ← Units.val_mul, ← val_coord_mul (U.gt e) p.1 p.2 x z hJ, Units.val_mul]
      ring) χ₀ hS Z x r hr z J hJ
  rw [hd χ₀ Z r z J hJ, Finset.sum_eq_zero, sub_zero] at H
  · exact H
  intro p _
  rw [hq χ₀ p Z r z J hJ]
  split_ifs with hp
  · by_cases h₁ : p.1 ∈ Λ
    · have h₂ : p.2 ∉ Λ := fun h₂ => hχ (hp ▸ Λ.add_mem h₁ h₂)
      rw [sval_eq_zero _ (hf' _ h₂) r z hJ, mul_zero, zero_mul]
    · rw [sval_eq_zero _ (hf _ h₁) r z hJ, zero_mul, zero_mul]
  · rfl
end GlobalTheory.MulSupp
