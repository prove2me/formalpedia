-- Prove2me | solution 1 for Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d8abe887-1670-5f83-83c9-f9b7d6e028eb

import Mathlib
import Theorems.Thm_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient
import Theorems.Thm_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
import Theorems.Thm_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset
import Theorems.Thm_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_represents_of_zariskiSheaf_of_openAffineCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

namespace GrassRepS1

variable {R : Type} [CommRing R] {S A : Type} [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]

lemma preimage_comp_algebraMap
    (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of S))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    (Spec.preimage g).hom.comp (algebraMap R S) = algebraMap R A := by
  rw [← Spec.map_preimage g, ← Spec.map_comp] at hg
  have h2 := Spec.map_injective hg
  rw [← CommRingCat.ofHom_hom (Spec.preimage g), ← CommRingCat.ofHom_comp] at h2
  exact congrArg CommRingCat.Hom.hom h2

noncomputable def ptAlgHom
    (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of S))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    S →ₐ[R] A :=
  { (Spec.preimage g).hom with
    commutes' := fun r => by
      have := congrArg (fun f : R →+* A => f r) (preimage_comp_algebraMap g hg)
      simpa using this }

lemma spec_map_ptAlgHom
    (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of S))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec.map (CommRingCat.ofHom (ptAlgHom g hg).toRingHom) = g := by
  conv_rhs => rw [← Spec.map_preimage g]
  rfl

end GrassRepS1

open GrassRepS1 in
theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) :
    ∃ (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        Module.Grassmannian A (A ⊗[R] M) k ≃
          {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
      (V : (Fin k → M) → Gr.Opens),
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : Module.Grassmannian A (A ⊗[R] M) k),
        (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1) ∧
      (⨆ x, V x = ⊤) ∧ (∀ x, IsAffineOpen (V x)) ∧
      (∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k),
          Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)) := by
  classical

  choose J hJ chart hcoord hnat using
    fun x : Fin k → M => Module.Grassmannian.exists_chart_equiv_algHom_symmetricAlgebra_quotient R M k x

  obtain ⟨X, p, pt, j, hptnat, hjopen, hjover, hjcover, hjchart⟩ :=
    AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover R
      (fun A _ _ => Module.Grassmannian A (A ⊗[R] M) k)
      (fun A B _ _ _ _ φ N => Module.Grassmannian.map φ N)
      (fun A _ _ N => Module.Grassmannian.map_id k (CommAlgCat.of R A) N)
      (fun A B C _ _ _ _ _ _ φ ψ N => Module.Grassmannian.map_comp k φ ψ N)
      (fun A _ _ n f hf B _ _ _ _ _ N hN =>
        Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away R M k A n f hf B N hN)
      (Fin k → M)
      (fun x A _ _ N => Function.Bijective fun v : Fin k → A =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i))
      (fun x A _ _ N =>
        Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset R M k x A N)
      (fun x => SymmetricAlgebra R (Fin k → M) ⧸ J x)
      (fun x A _ _ => chart x A)
      (fun x A B _ _ _ _ φ N h => by
        obtain ⟨h', e⟩ := (hnat x) A B φ N
        exact e)
      (fun K _ _ N => by
        obtain ⟨I, -, hI⟩ := Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top R M k M id
          (by simp) K N
        exact ⟨I, hI⟩)
  refine ⟨X, p, pt, fun x => (j x).opensRange, hptnat, ?_, fun x => isAffineOpen_opensRange (j x), ?_⟩
  ·
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨x, hx⟩ := hjcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx⟩
  · intro x A _ _ N
    constructor
    ·
      intro hsub
      have hsub' : Set.range (pt A N).1 ⊆ Set.range (j x) := hsub
      let g' := IsOpenImmersion.lift (j x) (pt A N).1 hsub'
      have hg'fac : g' ≫ j x = (pt A N).1 := IsOpenImmersion.lift_fac _ _ _
      have hg'over : g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R (Fin k → M) ⧸ J x))) =
          Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
        rw [← hjover x, ← Category.assoc, hg'fac]
        exact (pt A N).2
      let f : (SymmetricAlgebra R (Fin k → M) ⧸ J x) →ₐ[R] A := ptAlgHom g' hg'over
      let N' : {N : Module.Grassmannian A (A ⊗[R] M) k //
          Function.Bijective fun v : Fin k → A => ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} :=
        (chart x A).symm f
      have hN' : (pt A N'.1).1 = (pt A N).1 := by
        rw [hjchart x A N', Equiv.apply_symm_apply, spec_map_ptAlgHom, hg'fac]
      have hNN' : N'.1 = N := (pt A).injective (Subtype.ext hN')
      rw [← hNN']
      exact N'.2
    · intro hN
      rw [hjchart x A ⟨N, hN⟩]
      rintro _ ⟨y, rfl⟩
      exact ⟨(Spec.map (CommRingCat.ofHom (chart x A ⟨N, hN⟩).toRingHom)) y, rfl⟩

end S_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover
end P2MW
export P2MW.S_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover (solution)
