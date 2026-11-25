-- Prove2me | solution 1 for GlobalTheory.KS.Exist.exists_ksRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:43:43.51691+00:00
-- url     : https://prove2.me/submissions/09ec598f-9ce4-43de-916a-76c3419c70ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationAlongFibreOfSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticKodairaSpencerClass
import Theorems.Thm_GlobalTheory_KS_Exist_ptDer_add
import Theorems.Thm_GlobalTheory_KS_Exist_locDer_sub
import Theorems.Thm_GlobalTheory_KS_Exist_ex_per
import Theorems.Thm_GlobalTheory_KS_Exist_dom_open
import Theorems.Thm_GlobalTheory_KS_Exist_dom_inf
import Theorems.Thm_GlobalTheory_KS_Exist_dom_per
import Theorems.Thm_GlobalTheory_KS_Exist_val_hol
import Theorems.Thm_GlobalTheory_KS_Exist_fderiv_res
import Theorems.Thm_GlobalTheory_KS_Exist_fderiv_per
import Theorems.Thm_GlobalTheory_KS_Exist_ptDer_fderiv
import Theorems.Thm_GlobalTheory_KS_Exist_fderiv_const_eq
import Theorems.Thm_GlobalTheory_KS_Exist_ev_eq
import Theorems.Thm_GlobalTheory_KS_Exist_ptDer_ev
import Theorems.Thm_GlobalTheory_KS_Exist_ev_base
import Theorems.Thm_GlobalTheory_KS_Exist_ev_hol
import Theorems.Thm_GlobalTheory_KS_Exist_ev_per
import Theorems.Thm_GlobalTheory_KS_Exist_fderiv_field_hol
import Theorems.Thm_GlobalTheory_KS_Exist_exists_affine_dom
import Theorems.Thm_GlobalTheory_KS_VertFamily_ptDer_fderiv
import Theorems.Thm_GlobalTheory_KS_locDer_regular_coeff
import Theorems.Thm_GlobalTheory_T_existsUnique_uniformising_vector_vertical_tangent
import Theorems.Thm_GlobalTheory_T_exists_localDerivationAlongFibre_of_smooth
import Theorems.Thm_GlobalTheory_holomorphic_periodic_cocycle_coboundary
import Theorems.Thm_P2M_GlobalTheory_valAt__sub_69c6e35626ad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Exist
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
  (m : A₀.left ⟶ X)
variable {R : Type} [CommRing R] {p : X ⟶ Sp R} {D : R → ℂ} {W₀ : X.Opens}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.Exist
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  intro P₀ u Hm χ hu R _ x₀ X p m hp hm D hD
  choose d hd using fun i : X.affineOpens => GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth R x₀ _ X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose c hc using fun i j : X.affineOpens =>
    GlobalTheory.KS.locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hd i) (hd j))
  let C : X.affineOpens → X.affineOpens → (Fin P₀.g → ℂ) → Fin P₀.g → ℂ :=
    fun i j z a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (c i j a)
  have hC : ∀ i j z W f, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m W →
      ev u m i.1 (d i) z W f - ev u m j.1 (d j) z W f = fderiv ℂ (fn u m W f) z (C i j z) := by
    intro i j z W f hi hj hW
    have h : z ∈ dom u m (W ⊓ (i.1 ⊓ j.1)) := (dom_inf u m).2 ⟨hW, (dom_inf u m).2 ⟨hi, hj⟩⟩
    rw [ev_eq u m (hd i) inf_le_left (inf_le_right.trans inf_le_left) h,
      ev_eq u m (hd j) inf_le_left (inf_le_right.trans inf_le_right) h, ← valAt'_sub,
      hc i j _ inf_le_right _ z h, fderiv_res u m _ _ h]
  have hco : ∀ i j k z, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m k.1 → C i j z + C j k z = C i k z := by
    intro i j k z hi hj hk
    refine (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (ptDer_fderiv u m z (C i k z))
      (fun r => fderiv_const_eq u m hm.w r z _)).unique (fun W f hW => ?_) (fun _ _ _ => rfl)
    rw [map_add, ← hC i j z W f hi hj hW, ← hC j k z W f hj hk hW, ← hC i k z W f hi hk hW]
    ring
  choose t h hh hch using fun a : Fin P₀.g =>
    GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full X.affineOpens (fun i => dom u m i.1)
      (fun i j z => C i j z a) (fun i => dom_open u m _) (fun i l z hz => (dom_per u m l _ z).2 hz)
      (exists_affine_dom u m)
      (fun i j => (val_hol u m _ (c i j a)).mono fun z hz => (dom_inf u m).2 hz)
      (fun i j l z _ => by simp only [C, ex_per])
      (fun i j k z hz => congrFun (hco i j k z hz.1.1 hz.1.2 hz.2) a)
  choose κ hκ using exists_affine_dom u m
  let s : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ := fun z W f =>
    ev u m (κ z).1 (d (κ z)) z W f + fderiv ℂ (fn u m W f) z (fun a => h a (κ z) z)
  have hs : ∀ j z W f, z ∈ dom u m j.1 → z ∈ dom u m W →
      s z W f = ev u m j.1 (d j) z W f + fderiv ℂ (fn u m W f) z (fun a => h a j z) := by
    intro j z W f hj hW
    have e₁ := hC (κ z) j z W f (hκ z) hj hW
    have e₂ : C (κ z) j z = (fun a => h a j z) - fun a => h a (κ z) z :=
      funext fun a => hch a (κ z) j z ⟨hκ z, hj⟩
    rw [e₂, map_sub] at e₁
    simp only [s]
    linear_combination e₁
  refine ⟨Matrix.of t, s, fun z => ptDer_add (ptDer_ev u m (hd _) (hκ z)) (ptDer_fderiv u m z _), fun z r => ?_,
    fun W f z hz => ?_, fun l W f z hz => ?_⟩
  · simp only [s]
    rw [ev_base u m (hd _) (hκ z), fderiv_const_eq u m hm.w, add_zero]
  · have hz' : z ∈ dom u m (W ⊓ (κ z).1) := (dom_inf u m).2 ⟨hz, hκ z⟩
    have hn := (dom_open u m _).mem_nhds hz'
    have h₁ := (ev_hol u m (W₀ := (κ z).1) (d := d (κ z)) W f).add
      (fderiv_field_hol u m W f (S := dom u m (W ⊓ (κ z).1)) (fun y hy => ((dom_inf u m).1 hy).1)
        (fun a => h a (κ z)) fun a => (hh a (κ z)).1.mono fun y hy => ((dom_inf u m).1 hy).2)
    refine ((h₁.congr fun y hy => ?_).differentiableAt hn).differentiableWithinAt
    exact hs (κ z) y W f ((dom_inf u m).1 hy).2 ((dom_inf u m).1 hy).1
  · rw [hs (κ z) (z + l) W f ((dom_per u m l _ z).2 (hκ z)) ((dom_per u m l _ z).2 hz), ev_per, fderiv_per]
    have e : (fun a => h a (κ z) (z + l)) = (fun a => h a (κ z) z) + (Matrix.of t).mulVec (star (l : Fin P₀.g → ℂ)) :=
      funext fun a => (hh a (κ z)).2 l z (hκ z)
    rw [e, map_add]
    simp only [s]
    ring
end GlobalTheory.KS.Exist
