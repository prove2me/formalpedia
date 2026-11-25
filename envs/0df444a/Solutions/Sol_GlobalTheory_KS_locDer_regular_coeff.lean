-- Prove2me | solution 1 for GlobalTheory.KS.locDer_regular_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:48.524092+00:00
-- url     : https://prove2.me/submissions/3a2967aa-8c19-44fd-98ca-051948fdce51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
import Theorems.Thm_GlobalTheory_KS_VertReg_exists_cramer
import Theorems.Thm_GlobalTheory_KS_VertReg_val_res
import Theorems.Thm_GlobalTheory_KS_VertReg_ptDer_ptOf
import Theorems.Thm_GlobalTheory_KS_VertReg_ptOf_const
import Theorems.Thm_GlobalTheory_T_existsUnique_section_of_locally_given_values
import Theorems.Thm_GlobalTheory_T_existsUnique_uniformising_vector_vertical_tangent
import Theorems.Thm_GlobalTheory_T_exists_fibre_coords_det_fderiv_ne_zero_of_smooth
import Theorems.Thm_GlobalTheory_T_invariant_vectorField_abelianVariety_algebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.VertReg
private theorem exists_ringHom_eq_valAt'' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ φ : Γ(Y, U) →+* ℂ, ∀ f, valAt' x U f = φ f := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom, fun f => ?_⟩
  unfold valAt'
  rw [dif_pos h]
  rfl
private theorem valAt'_app_eq_valAt'_comp_moduli {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  by_cases hh : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · have hh' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hh
    rw [dif_pos hh, dif_pos hh']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have hh' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hh
    rw [dif_neg hh, dif_neg hh']
private theorem top_le_preimage_basicOpen_of_valAt'_ne_zero {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (g : Γ(Y, U))
    (hg : valAt' y U g ≠ 0) : ⊤ ≤ y ⁻¹ᵁ Y.basicOpen g := by
  unfold valAt' at hg
  rw [dif_pos h] at hg
  unfold valAt at hg
  have hu : IsUnit ((y.appLE U ⊤ h).hom g) := by
    have h1 := (isUnit_iff_ne_zero.2 hg).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h1
  have h1 : (Sp ℂ).basicOpen ((y.appLE U ⊤ h).hom g) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have h2 : (Sp ℂ).basicOpen ((y.appLE U ⊤ h).hom g) ≤ y ⁻¹ᵁ Y.basicOpen g := by
    rw [Scheme.preimage_basicOpen]
    exact (Scheme.basicOpen_res (Sp ℂ) ((y.app U).hom g) (homOfLE h).op).le.trans inf_le_right
  exact h1.ge.trans h2
private theorem top_le_preimage_preimage_inf {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) {U V : X.Opens}
    (h1 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ (U ⊓ V) :=
  fun _ ha => ⟨h1 ha, h2 ha⟩
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
end GlobalTheory.KS.VertReg
namespace GlobalTheory.KS
open VertReg
end GlobalTheory.KS
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
open VertReg
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(P₀.A.left, m ⁻¹ᵁ W)), LocDer P₀.A.hom p m (fun _ => 0) W₀ d → ∃ c : Fin P₀.g → Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f, ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) = fderiv ℂ (fn u m W f) z (fun a => valAt' (u.ex z).left (m ⁻¹ᵁ W₀) (c a)) := by
  classical
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb W₀ d hd
  have hq : ∀ z, (u.ex z).left ≫ P₀.A.hom = 𝟙 _ := fun z => by simp [Over.w (u.ex z)]
  have hw : ∀ z, ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀ → ∃ w : Fin P₀.g → ℂ, ∀ W f, z ∈ dom u m W →
      ptOf W₀ d (u.ex z).left W f = fderiv ℂ (fn u m W f) z w := fun z hz =>
    (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hsm hpb z _ (ptDer_ptOf hd _ hz)
      (fun r => ptOf_const hd _ (hq z) hz r)).exists
  let wf : (Fin P₀.g → ℂ) → Fin P₀.g → ℂ := fun z =>
    if hz : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀ then (hw z hz).choose else 0
  have hwf : ∀ z (hz : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀) W f, z ∈ dom u m W →
      ptOf W₀ d (u.ex z).left W f = fderiv ℂ (fn u m W f) z (wf z) := by
    intro z hz W f hzW
    simp only [wf, dif_pos hz]
    exact (hw z hz).choose_spec W f hzW
  have lin : ∀ (L : (Fin P₀.g → ℂ) →L[ℂ] ℂ) (v : Fin P₀.g → ℂ), L v = ∑ i, v i * L (Pi.single i 1) := by
    intro L v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (v i) : Fin P₀.g → ℂ) = v i • (Pi.single i (1 : ℂ) : Fin P₀.g → ℂ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [hs, map_smul, smul_eq_mul]
  choose D _ hDv using fun i : Fin P₀.g => GlobalTheory.T.invariant_vectorField_abelianVariety_algebraic P₀ u Hm χ hG (Pi.single i 1)
  have hfn : ∀ (W : X.Opens) (f : Γ(X, W)),
      (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) = fn u m W f := fun W f => by
    funext z'
    exact valAt'_app_eq_valAt'_comp_moduli _ m W f
  have hc : ∀ a, ∃ c : Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) →
      valAt' (u.ex z).left (m ⁻¹ᵁ W₀) c = wf z a := by
    intro a
    refine (GlobalTheory.T.existsUnique_section_of_locally_given_values P₀ u Hm χ hG (m ⁻¹ᵁ W₀) (fun z => wf z a) ?_).exists
    intro z hz
    obtain ⟨W, t, hzW, hdet⟩ := GlobalTheory.T.exists_fibre_coords_det_fderiv_ne_zero_of_smooth P₀ u Hm χ hG R x₀ X p m hsm hpb z
    have hzW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((𝟙 P₀.A.left) ⁻¹ᵁ (m ⁻¹ᵁ W)) := hzW
    let J : Matrix (Fin P₀.g) (Fin P₀.g) Γ(P₀.A.left, (𝟙 P₀.A.left) ⁻¹ᵁ (m ⁻¹ᵁ W)) :=
      fun i b => D i (m ⁻¹ᵁ W) ((m.app W).hom (t b))
    let e : Fin P₀.g → Γ(P₀.A.left, m ⁻¹ᵁ (W ⊓ W₀)) := fun b => d (W ⊓ W₀) (resG X inf_le_left (t b))
    have hJv : ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) → ∀ i b,
        valAt' (u.ex z').left _ (J i b) = fderiv ℂ (fn u m W (t b)) z' (Pi.single i 1) := by
      intro z' hz' i b
      rw [← hfn]
      exact hDv i (m ⁻¹ᵁ W) _ z' hz'
    obtain ⟨c, hcr⟩ := exists_cramer _ _ J e a
    refine ⟨_, c, inf_le_right.trans (fun _ hx => (inf_le_right : W ⊓ W₀ ≤ W₀) hx), ?_, ?_⟩
    · have hb : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P₀.A.left.basicOpen J.det := by
        refine top_le_preimage_basicOpen_of_valAt'_ne_zero _ _ hzW' _ ?_
        obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' _ _ hzW'
        rw [hφ, RingHom.map_det]
        convert hdet using 2
        ext i b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hφ, hJv z hzW i b]
        rfl
      exact fun x hx => ⟨hb hx, ⟨hzW hx, hz hx⟩⟩
    · intro z' hz'
      have h2 : ⊤ ≤ (u.ex z').left ⁻¹ᵁ m ⁻¹ᵁ (W ⊓ W₀) := fun x hx => (hz' hx).2
      have hW' : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W := fun x hx => (h2 hx).1
      have hW0 : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W₀ := fun x hx => (h2 hx).2
      refine hcr (u.ex z').left hz' (wf z') fun b => ?_
      have e1 : valAt' (u.ex z').left (m ⁻¹ᵁ (W ⊓ W₀)) (e b) = ptOf W₀ d (u.ex z').left W (t b) := rfl
      rw [e1, hwf z' hW0 W (t b) hW', lin]
      exact Finset.sum_congr rfl fun i _ => by rw [hJv z' hW' i b]
  choose c hcv using hc
  refine ⟨c, ?_⟩
  intro W hW f z hz
  have hz' : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W := hz
  have hz0 : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W₀ := fun x hx => hW (hz' hx)
  have e1 : valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) = ptOf W₀ d (u.ex z).left W f :=
    (val_res hd _ inf_le_left hW (top_le_preimage_preimage_inf _ m hz' hz0) f).symm
  rw [e1, hwf z hz0 W f hz]
  congr 1
  funext a
  exact (hcv a z hz0).symm
end GlobalTheory.KS
