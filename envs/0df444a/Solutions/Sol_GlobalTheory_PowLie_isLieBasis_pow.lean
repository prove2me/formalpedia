-- Prove2me | solution 1 for GlobalTheory.PowLie.isLieBasis_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:05.397825+00:00
-- url     : https://prove2.me/submissions/cef513a8-dfb6-4d9f-b23f-5ed367b5992a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Theorems.Thm_GlobalTheory_PowLie_isTangent_iff
import Theorems.Thm_GlobalTheory_PowLie_isLieComb_iff_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PowLie
variable {R : Type} [CommRing R]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
private theorem finset_prod_comp_of_isMonHom {X M N : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [MonObj M] [IsCommMonObj M]
    [MonObj N] [IsCommMonObj N] {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ M)) (h : M ⟶ N)
    [IsMonHom h] : (∏ i ∈ s, f i) ≫ h = ∏ i ∈ s, f i ≫ h :=
  map_prod (IsMonHom.monoidHom h X) f s
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
private theorem zeroPt_comp_one {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] :
    _root_.GlobalTheory.PowLie.zeroPt R ≫ (1 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) = η[G] := by
  rw [comp_one, Hom.one_def]
  simp
end GlobalTheory.PowLie
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowLie
variable {R : Type} [CommRing R]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PowLie
namespace _root_.GlobalTheory.PowLie
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G' G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j g : ℕ) (p : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPowGrp G' G j)
    (v : Fin g → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → ∃ v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G'),
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v' ∧ ∀ (i i' : Fin j) (k : Fin g),
        v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
  intro R _ G' G _ _ _ _ j g p v hv
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis at hv ⊢
  obtain ⟨htan, huniq⟩ := hv
  have hmon : ∀ i, IsMonHom (p.pr i) := p.hom
  let v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') := fun m =>
    Fan.IsLimit.lift p.lim (fun i' =>
      if (finProdFinEquiv.symm m).1 = i' then v (finProdFinEquiv.symm m).2 else 1)
  have hv' : ∀ (i i' : Fin j) (k : Fin g),
      v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
    intro i i' k
    exact (Fan.IsLimit.fac p.lim _ i').trans (by simp only [Equiv.symm_apply_apply])
  have hpr : ∀ (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') (i : Fin j), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent (w ≫ p.pr i) := by
    intro w i hw
    rw [_root_.GlobalTheory.PowLie.isTangent_iff] at hw ⊢
    rw [← Category.assoc, hw, IsMonHom.one_hom]
  have hcomb : ∀ (c : Fin (j * g) → R) (i' : Fin j),
      (∏ m, _root_.GlobalTheory.PowLie.sc (c m) ≫ v' m) ≫ p.pr i' =
        ∏ k, _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i', k))) ≫ v k := by
    intro c i'
    rw [finset_prod_comp_of_isMonHom, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
    have hterm : ∀ (i : Fin j) (k : Fin g),
        (_root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v' (finProdFinEquiv (i, k))) ≫
            p.pr i' =
          if i = i' then _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v k else 1 := by
      intro i k
      rw [Category.assoc, hv']
      split_ifs <;> simp [comp_one]
    simp only [hterm]
    rw [Fintype.prod_eq_single i' (fun i hi => by simp [hi])]
    simp
  refine ⟨v', ⟨fun m => ?_, fun w hw => ?_⟩, hv'⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [_root_.GlobalTheory.PowLie.isTangent_iff]
    refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
    change (_root_.GlobalTheory.PowLie.zeroPt R ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' =
      η[G'] ≫ p.pr i'
    rw [Category.assoc, hv', IsMonHom.one_hom]
    split_ifs
    · exact (_root_.GlobalTheory.PowLie.isTangent_iff _).1 (htan k)
    · exact zeroPt_comp_one
  · choose cc hcc hcc' using fun i => huniq (w ≫ p.pr i) (hpr w i hw)
    refine ⟨fun m => cc (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2, ?_, ?_⟩
    · beta_reduce
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod]
      refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
      change w ≫ p.pr i' = (∏ m, _) ≫ p.pr i'
      rw [hcomb, (_root_.GlobalTheory.PowLie.isLieComb_iff_prod _ _ _).1 (hcc i')]
      simp
    · intro c' hc'
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod] at hc'
      funext m
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
      have h := hcc' i (fun k => c' (finProdFinEquiv (i, k))) (by
        beta_reduce
        rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod, hc', hcomb])
      simpa using congrFun h k
end _root_.GlobalTheory.PowLie
end GlobalTheory.PowLie
