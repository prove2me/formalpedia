-- Prove2me | solution 1 for GlobalTheory.subsingleton_cechAbH_succ_of_isFlasque
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:20.550741+00:00
-- url     : https://prove2.me/submissions/1289bbb8-f548-435b-81bf-7af952bd0e73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Theorems.Thm_GlobalTheory_cechAbAug_apply
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_cechAbCubeMap_app_apply
import Theorems.Thm_GlobalTheory_cechAbHMap_id
import Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff_cube
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_of_faces
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_GlobalTheory_presheafCechHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_presheafCube_exactAt_zero_one
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.cechAbCubeMap_app_apply
attribute [local simp] GlobalTheory.cechAbHMap_id
attribute [local simp] GlobalTheory.cechAbHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id
attribute [local simp] GlobalTheory.presheafCechHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


attribute [local simp] GlobalTheory.cechAbAug_apply
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe w v u
noncomputable section
namespace GlobalTheory
section Presheaf
variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (presheafRes P h))
include hP hs
end Presheaf
section Ab
variable {T : TopCat.{w}} {ι : Type}
variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque]
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] in
private theorem cubeComplex_exactAt_one_of_hom_surj_empty_inj_nonempty {A B : _root_.GlobalTheory.Cube ι R} (φ : A ⟶ B)
    (hsurj : ∀ s : Finset ι, s = ∅ → Function.Surjective (φ.app s))
    (hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ.app s))
    (hB : (_root_.GlobalTheory.cubeComplex B).ExactAt 1) : (_root_.GlobalTheory.cubeComplex A).ExactAt 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, _root_.GlobalTheory.cubeComplex_exactAt_succ_iff] at hB ⊢
  have comm : ∀ p (x : A.Term p), (_root_.GlobalTheory.cubeComplexMap φ).f (p + 1) (A.d p x) =
      B.d p ((_root_.GlobalTheory.cubeComplexMap φ).f p x) := by
    intro p x
    have := congrArg (fun f => f.hom x) ((_root_.GlobalTheory.cubeComplexMap φ).comm p (p + 1))
    simp only [_root_.GlobalTheory.cubeComplex, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply] at this
    exact this.symm
  have dd : ∀ y : A.Term 0, A.d 1 (A.d 0 y) = 0 := by
    intro y
    have := congrArg (fun f => f.hom y) ((_root_.GlobalTheory.cubeComplex A).d_comp_d 0 1 2)
    simpa [_root_.GlobalTheory.cubeComplex, LinearMap.comp_apply] using this
  have inj1 : Function.Injective ((_root_.GlobalTheory.cubeComplexMap φ).f 1) := by
    intro x y hxy
    funext s
    apply hinj s.1 (Finset.card_pos.mp (by rw [s.2]; norm_num))
    exact congrFun hxy s
  have surj0 : Function.Surjective ((_root_.GlobalTheory.cubeComplexMap φ).f 0) := by
    intro y
    refine ⟨fun s => (hsurj s.1 (Finset.card_eq_zero.mp s.2) (y s)).choose, ?_⟩
    funext s
    exact (hsurj s.1 (Finset.card_eq_zero.mp s.2) (y s)).choose_spec
  intro x
  constructor
  · intro hx
    have h1 : B.d 1 ((_root_.GlobalTheory.cubeComplexMap φ).f 1 x) = 0 := by
      rw [← comm 1 x]
      change (_root_.GlobalTheory.cubeComplexMap φ).f 2 (A.d 1 x) = 0
      rw [show A.d 1 x = 0 from hx]
      exact map_zero _
    obtain ⟨y, hy⟩ := (hB ((_root_.GlobalTheory.cubeComplexMap φ).f 1 x)).1 h1
    obtain ⟨z, rfl⟩ := surj0 y
    exact ⟨z, inj1 ((comm 0 z).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact dd y
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (_root_.GlobalTheory.presheafRes P h)) in
include hP hs in
private theorem cubeComplex_presheafCube_exactAt_one (V : Opens T) (U : ι → Opens T) :
    (_root_.GlobalTheory.cubeComplex (_root_.GlobalTheory.presheafCube P V U)).ExactAt 1 := by
  have h : ∀ s, _root_.GlobalTheory.cechOpen (V ⊓ ⨆ i, U i) U s ≤ _root_.GlobalTheory.cechOpen V U s :=
    fun s => _root_.GlobalTheory.cechOpen_mono inf_le_left (fun _ => le_rfl) s
  refine cubeComplex_exactAt_one_of_hom_surj_empty_inj_nonempty (_root_.GlobalTheory.presheafCubeRes P h) ?_ ?_
    (_root_.GlobalTheory.presheafCube_exactAt_zero_one hP (V := V ⊓ ⨆ i, U i) (U := U) inf_le_right).2
  · rintro s rfl
    exact hs (h ∅)
  · intro s hs' x y hxy
    have h' : _root_.GlobalTheory.cechOpen V U s ≤ _root_.GlobalTheory.cechOpen (V ⊓ ⨆ i, U i) U s := by
      intro z hz
      rw [_root_.GlobalTheory.mem_cechOpen] at hz ⊢
      obtain ⟨j, hj⟩ := hs'
      exact ⟨⟨hz.1, Opens.mem_iSup.mpr ⟨j, hz.2 j hj⟩⟩, hz.2⟩
    have back : ∀ (O O' : Opens T) (h₁ : O' ≤ O) (h₂ : O ≤ O') (w : P.obj (op O)),
        P.map (homOfLE h₂).op (P.map (homOfLE h₁).op w) = w := by
      intro O O' h₁ h₂ w
      rw [← ConcreteCategory.comp_apply, ← P.map_comp,
        show (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 _ from Subsingleton.elim _ _]
      simp
    have key : ∀ w, P.map (homOfLE h').op ((_root_.GlobalTheory.presheafCubeRes P h).app s w) = w :=
      fun w => back _ _ (h s) h' w
    rw [← key x, ← key y, hxy]
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (_root_.GlobalTheory.presheafRes P h)) in
include hP hs in
private theorem cubeComplex_presheafCube_exactAt_add_one_of_card (n : ℕ) :
    ∀ {α : Type} [LinearOrder α] [Fintype α], Fintype.card α = n →
      ∀ (V : Opens T) (U : α → Opens T) (p : ℕ),
        (_root_.GlobalTheory.cubeComplex (_root_.GlobalTheory.presheafCube P V U)).ExactAt (p + 1) := by
  induction n with
  | zero =>
    intro α _ _ hcard V U p
    rw [_root_.GlobalTheory.cubeComplex_exactAt_succ_iff]
    have : Subsingleton ((_root_.GlobalTheory.presheafCube P V U).Term (p + 1)) :=
      _root_.GlobalTheory.Cube.subsingleton_term _ (by omega)
    have : Subsingleton ((_root_.GlobalTheory.presheafCube P V U).Term (p + 1 + 1)) :=
      _root_.GlobalTheory.Cube.subsingleton_term _ (by omega)
    intro x
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    intro α _ _ hcard V U p
    cases p with
    | zero => exact cubeComplex_presheafCube_exactAt_one hP hs V U
    | succ p =>
      obtain ⟨i⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      let e : {j : α // j ≠ i} ↪o α := OrderEmbedding.subtype _
      have he : Set.range e = {i}ᶜ := by
        ext j
        simp [e]
      have hcard' : Fintype.card {j : α // j ≠ i} = n := by
        simp [Fintype.card_subtype_compl, hcard]
      apply _root_.GlobalTheory.cubeComplex_exactAt_succ_of_faces he
      · exact (ih hcard' V (fun k => U (e k)) (p + 1)).of_iso
          ((_root_.GlobalTheory.cubeFunctor _ R).mapIso (_root_.GlobalTheory.presheafCubeLowerFaceIso P V U e)).symm
      · exact (ih hcard' (V ⊓ U i) (fun k => U (e k)) p).of_iso
          ((_root_.GlobalTheory.cubeFunctor _ R).mapIso (_root_.GlobalTheory.presheafCubeUpperFaceIso P V U e i)).symm
end Ab
section Modules
variable {X : Scheme.{u}} {ι : Type} (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) [hF : TopCat.Presheaf.IsFlasque (X := X.toPresheafedSpace.carrier) F.presheaf]
include hF
variable [LinearOrder ι] [Finite ι]
end Modules
end GlobalTheory
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{w}} {ι : Type}
variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque]
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
variable {T : TopCat.{w}} {ι : Type}
variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (V : Opens T) (U : ι → Opens T) (p : ℕ) :
    Subsingleton (_root_.GlobalTheory.cechAbH F.obj V U (p + 1)) := by
  have := Fintype.ofFinite ι
  have hP := _root_.GlobalTheory.isSheaf_comp_abToIntModule F.cond
  have hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W),
      Function.Surjective (_root_.GlobalTheory.presheafRes (F.obj ⋙ _root_.GlobalTheory.abToIntModule) h) := by
    intro W W' h
    have : Epi (F.obj.map (homOfLE h).op) := TopCat.Presheaf.IsFlasque.epi _
    exact (AddCommGrpCat.epi_iff_surjective _).mp this
  have hex := cubeComplex_presheafCube_exactAt_add_one_of_card hP hs _ rfl V U (p + 1)
  have hcech := (_root_.GlobalTheory.cechComplex_exactAt_succ_iff_cube _ p).mpr hex
  exact ModuleCat.subsingleton_of_isZero hcech.isZero_homology
end _root_.GlobalTheory
end GlobalTheory
