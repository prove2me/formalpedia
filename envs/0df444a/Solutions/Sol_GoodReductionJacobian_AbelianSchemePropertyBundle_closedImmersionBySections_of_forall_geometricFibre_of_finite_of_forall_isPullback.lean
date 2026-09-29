-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f7a28790-11a8-5ec0-b6d4-6c35220f414b

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      Scheme.Modules.ClosedImmersionBySections
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M)
        (pullback.snd f (Spec.map (CommRingCat.ofHom sk))))
    (hfg : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      Module.Finite S Γ(M, ⊤) ∧ Module.Projective S Γ(M, ⊤))
    (hbc : ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
        (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))),
        letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
        letI : Module S' Γ((Scheme.Modules.pullback gA).obj M, gA ⁻¹ᵁ ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
        letI : Algebra S S' := φ.toAlgebra
        ∃ e : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj M, gA ⁻¹ᵁ ⊤),
          ∀ (s' : S') (τ : Γ(M, ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection gA τ) :
    Scheme.Modules.ClosedImmersionBySections M f := by
  classical
  letI modS : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
  haveI : IsProper f := hA.proper

  haveI : Module.Finite S Γ(M, ⊤) := hfg.1
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := Γ(M, ⊤))
  let σ : Fin (n + 1) → Γ(M, ⊤) := Fin.cons 0 s
  have hσ : Submodule.span S (Set.range σ) = ⊤ := by
    refine eq_top_iff.mpr (hs ▸ Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, by simp [σ]⟩

  have hspanK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
      (t : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤)),
      letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M,
          (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤
            ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) le_top).hom
      ∃ c : Fin (n + 1) → k, t = ∑ i, c i •
        Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) (σ i) := by
    intro k _ _ sk t
    exact AlgebraicGeometry.Scheme.Modules.forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct
      f M σ hσ k sk (Limits.pullback f (Spec.map (CommRingCat.ofHom sk)))
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))) (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))
      (IsPullback.of_hasPullback _ _) (hbc k sk _ _ _ (IsPullback.of_hasPullback _ _)) t
  have hgenK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
      (x' : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)))),
      ∃ (t : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤))
        (U' : (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Opens), x' ∈ U' ∧ Scheme.Modules.IsFrameOn t U' := by
    intro k _ _ sk x'
    obtain ⟨N', 𝔔, -⟩ := hfib k sk
    obtain ⟨j, U', hx', hfr⟩ := 𝔔.exists_mem_isFrameOn x'
    exact ⟨𝔔.σ j, U', hx', hfr⟩

  have hfr : ∀ x : ↥A, ∃ (i : Fin (n + 1)) (U : A.Opens), x ∈ U ∧ Scheme.Modules.IsFrameOn (σ i) U :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection
      f M hM σ hgenK hspanK
  let U : Fin (n + 1) → A.Opens := fun i => ⨆ V : {V : A.Opens // Scheme.Modules.IsFrameOn (σ i) V}, V.1
  have hUframe : ∀ i, Scheme.Modules.IsFrameOn (σ i) (U i) := fun i =>
    AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2 (fun V : {V : A.Opens // Scheme.Modules.IsFrameOn (σ i) V} => V.1)
      fun V => V.2
  have hUtop : iSup U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, V, hxV, hV⟩ := hfr x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩⟩
  obtain ⟨𝔓, h𝔓σ, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top f M n σ U hUtop
    (fun i V hV => (hUframe i) le_top hV)
  refine ⟨n, 𝔓, ?_⟩

  refine AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion f (ProjSpace.π S n)
    𝔓.toProj 𝔓.toProj_π fun k _ _ sk => ?_
  letI : Algebra S k := sk.toAlgebra
  obtain ⟨𝔓', h𝔓'σ, h𝔓'map, -⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S k)))) 𝔓
  refine ⟨Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), _, Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk)),
    ProjSpace.π k n, 𝔓'.toProj, Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)), ProjSpace.map S k n,
    IsPullback.of_hasPullback _ _, ProjSpace.isPullback_map S k n, 𝔓'.toProj_π, h𝔓'map.symm, ?_⟩
  refine AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection
    f M σ k sk (hfib k sk) (hspanK k sk) 𝔓' fun i => ?_
  rw [h𝔓'σ i, h𝔓σ]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback (solution)
