-- Prove2me | solution 1 for GlobalTheory.existsUnique_section_of_locally_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:30.270514+00:00
-- url     : https://prove2.me/submissions/077f5521-1554-482d-b7d3-082eb6dab0c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.GlueFn
end GlobalTheory.GlueFn
namespace GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma exists_complex_section_through_closed_point (X : Scheme) (p : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ q : Spec (CommRingCat.of ℂ) ⟶ X, q ≫ p = 𝟙 _ ∧ ∀ s, q.base s = x := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ p) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = X.fromSpecResidueField x ≫ p :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hφ] at h2
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  letI := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ (X.residueField x) := hft
  haveI : Module.Finite ℂ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing ℂ _
  have hsurj : Function.Surjective (algebraMap ℂ (X.residueField x)) := by
    apply IsSepClosed.algebraMap_surjective
  let e := RingEquiv.ofBijective (algebraMap ℂ (X.residueField x))
    ⟨(algebraMap ℂ _).injective, hsurj⟩
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ)
    ext a
    exact e.symm_apply_apply a
  · intro s
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma valAt'_sub_of_top_le {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (a b : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U (a - b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a - _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dif_pos hU, dif_pos hU, dif_pos hU]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  simp only [map_sub]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma not_mem_basicOpen_of_valAt'_eq_zero {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)
    (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U) (f : Γ(X, U)) (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U f = 0)
    (s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) : q.base s ∉ X.basicOpen f := by
  intro hs
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at hf
  rw [dif_pos hU] at hf
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hf
  have h0 : q.appLE U ⊤ hU f = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hf
    simpa using this
  have hmem : s ∈ q ⁻¹ᵁ X.basicOpen f := hs
  rw [Scheme.Hom.preimage_basicOpen] at hmem
  have hres : (Spec (CommRingCat.of ℂ)).basicOpen (q.appLE U ⊤ hU f) =
      ⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) := by
    rw [← Scheme.basicOpen_res]
    rfl
  rw [h0, Scheme.basicOpen_zero] at hres
  have : s ∈ (⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) :
      (Spec (CommRingCat.of ℂ)).Opens) := ⟨trivial, hmem⟩
  rw [← hres] at this
  exact this
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma valAt'_presheaf_map {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) {U V : X.Opens} (i : V ⟶ U)
    (hV : ⊤ ≤ q ⁻¹ᵁ V) (a : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q V (X.presheaf.map i.op a) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := fun s hs => i.le (hV hs)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dif_pos hU, dif_pos hV]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  rw [← Scheme.Hom.map_appLE q hV i.op]
  rfl
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct ContDiff
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (P₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), _root_.GlobalTheory.KS.GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
  intro P₀ u Hm χ _ O h H
  haveI := P₀.smoothDim
  have hsm : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g P₀.A.hom
  haveI := hsm
  haveI : IsReduced P₀.A.left := _root_.GlobalTheory.isReduced_of_smooth_complex _ _ hsm
  haveI : JacobsonSpace P₀.A.left := LocallyOfFiniteType.jacobsonSpace P₀.A.hom
  have hpt : ∀ y : P₀.A.left, IsClosed ({y} : Set P₀.A.left) →
      ∃ z, ∀ s, (u.ex z).left.base s = y := by
    intro y hy
    obtain ⟨q, hq, hqy⟩ := exists_complex_section_through_closed_point P₀.A.left P₀.A.hom y hy
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk q hq : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ P₀.A)
    exact ⟨z, fun s => by rw [hz]; exact hqy s⟩
  have hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ := IsLocalRing.closedPoint ℂ
  have huniq : ∀ (V : P₀.A.left.Opens) (a b : Γ(P₀.A.left, V)), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V a = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V b) → a = b := by
    intro V a b hab
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
    by_contra hne
    obtain ⟨y, hyB, hyc⟩ := nonempty_inter_closedPoints
      ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
      (P₀.A.left.basicOpen (a - b)).isOpen.isLocallyClosed
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ V := fun s _ => by
      show (u.ex z).left.base s ∈ V
      rw [hz]
      exact P₀.A.left.basicOpen_le _ hyB
    have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V (a - b) = 0 := by
      rw [valAt'_sub_of_top_le _ _ hzV, hab z hzV, sub_self]
    exact not_mem_basicOpen_of_valAt'_eq_zero _ _ hzV _ h0 hs₀ (by rw [hz]; exact hyB)
  have hloc : ∀ w : {z // ⊤ ≤ (u.ex z).left ⁻¹ᵁ O}, ∃ (O' : P₀.A.left.Opens)
      (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex w.1).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z' := fun w => H w.1 w.2
  choose W aW hWO hWz hWv using hloc
  have hcover : O ≤ iSup W := by
    by_contra hle
    have hZ : ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ).Nonempty := by
      rw [← Set.diff_eq, Set.diff_nonempty]
      exact hle
    have hZlc : IsLocallyClosed ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ) :=
      ⟨O, ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ, O.isOpen, (iSup W).isOpen.isClosed_compl, rfl⟩
    obtain ⟨y, ⟨hyO, hyW⟩, hyc⟩ := nonempty_inter_closedPoints hZ hZlc
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O := fun s _ => by
      show (u.ex z).left.base s ∈ O
      rw [hz]
      exact hyO
    have hyz : y ∈ W ⟨z, hzO⟩ := by
      rw [← hz hs₀]
      exact hWz ⟨z, hzO⟩ (show hs₀ ∈ (⊤ : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) from trivial)
    exact hyW (TopologicalSpace.Opens.mem_iSup.mpr ⟨_, hyz⟩)
  have hcompat : TopCat.Presheaf.IsCompatible P₀.A.left.sheaf.obj W aW := by
    intro i j
    apply huniq
    intro z hz
    have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W i := fun s hs => (inf_le_left : W i ⊓ W j ≤ W i) (hz hs)
    have hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W j := fun s hs => (inf_le_right : W i ⊓ W j ≤ W j) (hz hs)
    erw [valAt'_presheaf_map _ _ hz, valAt'_presheaf_map _ _ hz]
    rw [hWv i z hi, hWv j z hj]
  obtain ⟨a, ha, -⟩ := P₀.A.left.sheaf.existsUnique_gluing' W O (fun i => homOfLE (hWO i))
    hcover aW hcompat
  have hval : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
    intro z hz
    rw [← valAt'_presheaf_map (u.ex z).left (homOfLE (hWO ⟨z, hz⟩)) (hWz ⟨z, hz⟩) a]
    erw [ha ⟨z, hz⟩]
    exact hWv ⟨z, hz⟩ z (hWz ⟨z, hz⟩)
  refine ⟨a, hval, fun b hb => huniq O b a fun z hz => ?_⟩
  rw [hb z hz, hval z hz]
end _root_.GlobalTheory
end GlobalTheory
