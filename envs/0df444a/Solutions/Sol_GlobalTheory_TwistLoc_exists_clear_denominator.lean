-- Prove2me | solution 1 for GlobalTheory.TwistLoc.exists_clear_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:27.625804+00:00
-- url     : https://prove2.me/submissions/f3ec2124-691c-4c03-a104-1ea344dbbbd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_GlobalTheory_TwistLoc_exists_sec_of_cover
import Theorems.Thm_GlobalTheory_TwistLoc_gc_mul
import Theorems.Thm_GlobalTheory_TwistLoc_gs_cst
import Theorems.Thm_GlobalTheory_TwistLoc_exists_numerator
import Theorems.Thm_GlobalTheory_TwistLoc_exists_annihilator
import Theorems.Thm_GlobalTheory_SecPull_trF_comp
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
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}}
variable {Rm : Type} [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
  {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
  (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
include H
namespace GlobalTheory.TwistLoc
theorem _root_.solution [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (r ≫ h) z (LB.wchart L φ j) (s.f j) =
        gc (r ≫ h ≫ π) z t * gs r z (LB.wchart L (fun k => h ≫ φ k) j) (s'.f j) := by
  classical
  have loc : ∀ y : Y, ∃ (p : K → L.ι) (V : Y.Opens), IsAffineOpen V ∧ y ∈ V ∧ V ≤ LB.wchart L φ p := fun y => by
    choose p hp using fun k => exists_chart hL (φ k y)
    obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ (LB.wchart L φ p : Set Y) from Set.mem_iInter.2 hp) (LB.wchart L φ p).isOpen
    exact ⟨p, V, hV, hy, hle⟩
  choose p V hV hy hle using loc
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set Y)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  have cov : ∀ y, ∃ i : S, y ∈ V i := fun y => by
    obtain ⟨i, hi, h'⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h'⟩
  have le' : ∀ i, h ⁻¹ᵁ V i ≤ LB.wchart L (fun k => h ≫ φ k) (p i) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hle i hy) k
  choose t ht a ha using fun i : S => exists_numerator M H (hV i)
    ((Y'.presheaf.map (homOfLE (le' i)).op).hom (s'.f (p i)))
  obtain ⟨T, hT, a', ha'⟩ : ∃ T ∈ M, ∃ a' : ∀ i : S, Γ(Y, V i), ∀ (i : S) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z),
      h (r z) ∈ V i → gs (r ≫ h) z (V i) (a' i) =
        gc (r ≫ h ≫ π) z T * gs r z (LB.wchart L (fun k => h ≫ φ k) (p i)) (s'.f (p i)) := by
    refine ⟨∏ i, t i, prod_mem fun i _ => ht i, fun i => (cst π _).hom (∏ j ∈ Finset.univ.erase i, t j) * a i,
      fun i Z r z hz => ?_⟩
    rw [gs_mul (r ≫ h) z _ hz, gs_cst π (r ≫ h) z _ hz, ha i Z r z hz, gs_res r z (le' i) hz (s'.f (p i)), Category.assoc,
      ← _root_.mul_assoc, ← gc_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have ov : ∀ i i' : S, ∃ u ∈ M, ∀ y, y ∈ V i → y ∈ V i' → gc π y u * gs (𝟙 Y) y _ (a' i) =
      gc π y u * ((trF φ ε (𝟙 Y) y (p i) (p i')).val * gs (𝟙 Y) y _ (a' i')) := fun i i' => by
    have lw : V i ⊓ V i' ≤ LB.wchart L φ (p i) ⊓ LB.wchart L φ (p i') := inf_le_inf (hle i) (hle i')
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V i ⊓ V i' → gs r z (V i ⊓ V i')
        ((Y.presheaf.map (homOfLE lw).op).hom ((LB.LinComb L φ ε).g (p i) (p i')).val *
          (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V i' ≤ V i')).op).hom (a' i')) =
        (trF φ ε r z (p i) (p i')).val * gs r z _ (a' i') := fun Z r z hz =>
      (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ (lw hz) _).trans
        (congrArg Units.val (gm_linComb L φ ε r z _ _ (lw hz).1 (lw hz).2)))) (gs_res r z _ hz _))
    obtain ⟨u, hu, e⟩ := exists_annihilator M H (U := V i ⊓ V i')
      (QuasiSeparatedSpace.inter_isCompact _ _ (V i).isOpen (hV i).isCompact (V i').isOpen (hV i').isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _)
      ((Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V i' ≤ V i)).op).hom (a' i)) _ (fun y hy => by
        refine (gs_res h y _ hy _).trans (Eq.trans ?_ (v _ h y hy).symm)
        have e₁ := ha' i _ (𝟙 Y') y hy.1
        have e₂ := ha' i' _ (𝟙 Y') y hy.2
        have e₃ := SecPull.trF_comp (L := L) (F := 𝟙 X) (φ' := fun k => h ≫ φ k) (φ := φ) (h := h)
          (fun k => Category.comp_id _) ε (𝟙 Y') y (p i) (p i')
        simp only [Category.id_comp, Category.comp_id] at e₁ e₂ e₃
        rw [e₁, e₂, sec_trans s' (𝟙 Y') y (le' i hy.1) (le' i' hy.2), e₃, mul_left_comm])
    refine ⟨u, hu, fun y h₁ h₂ => ?_⟩
    have e' := e y ⟨h₁, h₂⟩
    rwa [v _ (𝟙 Y) y ⟨h₁, h₂⟩, gs_res (𝟙 Y) y (inf_le_left : V i ⊓ V i' ≤ V i) ⟨h₁, h₂⟩] at e'
  choose u hu hov using ov
  let U : R := ∏ q : S × S, u q.1 q.2
  obtain ⟨s, hs⟩ := exists_sec_of_cover hL φ ε (fun i : S => V i) cov (fun i => p i) (fun i => hle i)
    (fun i => (cst π _).hom U * a' i) (fun i i' y h₁ h₂ => by
      obtain ⟨c, hc⟩ : u i i' ∣ U := Finset.dvd_prod_of_mem (fun q : S × S => u q.1 q.2) (Finset.mem_univ (i, i'))
      rw [gs_mul _ y _ h₁, gs_mul _ y _ h₂, gs_cst π _ y _ h₁, gs_cst π _ y _ h₂, Category.id_comp, hc, mul_comm _ c,
        gc_mul, _root_.mul_assoc, hov i i' y h₁ h₂]
      ring)
  refine ⟨U * T, mul_mem (prod_mem fun q _ => hu q.1 q.2) hT, s, fun Z r z j hj => ?_⟩
  obtain ⟨i, hi⟩ := cov (h (r z))
  have e₃ := SecPull.trF_comp (L := L) (F := 𝟙 X) (φ' := fun k => h ≫ φ k) (φ := φ) (h := h)
    (fun k => Category.comp_id _) ε r z j (p i)
  simp only [Category.comp_id] at e₃
  rw [hs Z (r ≫ h) z i j hi (wchart_comp_le L φ h j hj), gs_mul (r ≫ h) z _ hi, gs_cst π (r ≫ h) z _ hi,
    ha' i Z r z hi, sec_trans s' r z hj (le' i hi), e₃, gc_mul, Category.assoc]
  ring
end GlobalTheory.TwistLoc
