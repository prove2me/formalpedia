-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ed3d155e-98c3-5a78-9f39-9e3e2eee595f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace Ws23ET

p2m_open "AlgebraicGeometry.OModulePresheaf Opposite"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (n : ℕ)
  (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)

section EigenMul

variable {χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R} {U : A.Opens}

theorem eigenMul_add_left (s s' : (L.eigenSubdatum n hG χ).obj U) (t : (L.eigenSubdatum n hG ψ).obj U) :
    L.eigenMul n hG (s + s') t = L.eigenMul n hG s t + L.eigenMul n hG s' t :=
  Subtype.ext (add_mul (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s.1) (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s'.1)
    (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t.1))

theorem eigenMul_add_right (s : (L.eigenSubdatum n hG χ).obj U) (t t' : (L.eigenSubdatum n hG ψ).obj U) :
    L.eigenMul n hG s (t + t') = L.eigenMul n hG s t + L.eigenMul n hG s t' :=
  Subtype.ext (mul_add (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s.1) (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t.1)
    (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t'.1))

theorem eigenMul_smul_left (a : Γ(A, U)) (s : (L.eigenSubdatum n hG χ).obj U) (t : (L.eigenSubdatum n hG ψ).obj U) :
    L.eigenMul n hG (a • s) t = a • L.eigenMul n hG s t :=
  Subtype.ext (mul_assoc (((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a)
    (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s.1) (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t.1))

theorem eigenMul_smul_right (a : Γ(A, U)) (s : (L.eigenSubdatum n hG χ).obj U) (t : (L.eigenSubdatum n hG ψ).obj U) :
    L.eigenMul n hG s (a • t) = a • L.eigenMul n hG s t :=
  Subtype.ext (mul_left_comm (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s.1)
    (((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a) (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t.1))

theorem eigenMul_res {U V : A.Opens} (h : V ≤ U) (s : (L.eigenSubdatum n hG χ).obj U) (t : (L.eigenSubdatum n hG ψ).obj U) :
    (L.eigenSubdatum n hG (χ * ψ)).res h (L.eigenMul n hG s t) =
      L.eigenMul n hG ((L.eigenSubdatum n hG χ).res h s) ((L.eigenSubdatum n hG ψ).res h t) :=
  Subtype.ext (map_mul (A.presheaf.map
    (homOfLE ((TopologicalSpace.Opens.map (L.schemeNsmul n).base).monotone h)).op).hom _ _)

end EigenMul

section Pairing

variable {χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R}
  (N₁ N₂ N₃ : A.Modules)
  (φ₁ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₁) (L.eigenSubdatum n hG χ))
  (φ₂ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₂) (L.eigenSubdatum n hG ψ))
  (ψ₃ : OModulePresheaf.Hom (L.eigenSubdatum n hG (χ * ψ)) (OModulePresheaf.ofModules f N₃))

noncomputable def pairing (U : A.Opens) : Γ(N₁, U) →ₗ[Γ(A, U)] Γ(N₂, U) →ₗ[Γ(A, U)] Γ(N₃, U) :=
  LinearMap.mk₂ Γ(A, U)
    (fun s t => (ψ₃.app U (L.eigenMul n hG (φ₁.app U s) (φ₂.app U t)) : Γ(N₃, U)))
    (fun s s' t => by
      show ψ₃.app U _ = ψ₃.app U _ + ψ₃.app U _
      rw [← map_add, ← eigenMul_add_left, ← map_add]; rfl)
    (fun a s t => by
      show ψ₃.app U _ = a • ψ₃.app U _
      rw [← ψ₃.app_smul, ← eigenMul_smul_left, ← φ₁.app_smul]; rfl)
    (fun s t t' => by
      show ψ₃.app U _ = ψ₃.app U _ + ψ₃.app U _
      rw [← map_add, ← eigenMul_add_right, ← map_add]; rfl)
    (fun a s t => by
      show ψ₃.app U _ = a • ψ₃.app U _
      rw [← ψ₃.app_smul, ← eigenMul_smul_right, ← φ₂.app_smul]; rfl)

theorem pairing_apply (U : A.Opens) (s : Γ(N₁, U)) (t : Γ(N₂, U)) :
    pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ U s t = ψ₃.app U (L.eigenMul n hG (φ₁.app U s) (φ₂.app U t)) := rfl

theorem map_pairing_le {U V : A.Opens} (hVU : V ≤ U) (s : Γ(N₁, U)) (t : Γ(N₂, U)) :
    N₃.presheaf.map (homOfLE hVU).op (pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ U s t) =
      pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ V (N₁.presheaf.map (homOfLE hVU).op s) (N₂.presheaf.map (homOfLE hVU).op t) := by
  rw [pairing_apply, pairing_apply]
  have h3 := ψ₃.naturality_apply hVU (L.eigenMul n hG (φ₁.app U s) (φ₂.app U t))
  rw [eigenMul_res, ← φ₁.naturality_apply, ← φ₂.naturality_apply] at h3
  exact h3.symm

theorem map_pairing {U V : A.Opens} (i : V ⟶ U) (s : Γ(N₁, U)) (t : Γ(N₂, U)) :
    N₃.presheaf.map i.op (pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ U s t) =
      pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ V (N₁.presheaf.map i.op s) (N₂.presheaf.map i.op t) :=
  map_pairing_le L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ i.le s t

end Pairing

section Frames

variable {χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R} (N : A.Modules)
  (φ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N) (L.eigenSubdatum n hG χ))
  (ψ' : OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.ofModules f N))
  (h : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U), φ.app U (ψ'.app U s) = s)
  (h' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N).obj U), ψ'.app U (φ.app U s) = s)

noncomputable def secOf (V : A.Opens) (s : (L.eigenSubdatum n hG χ).obj V) : Γ(N, V) := ψ'.app V s

theorem map_secOf {V W : A.Opens} (hW : W ≤ V) (s : (L.eigenSubdatum n hG χ).obj V) :
    N.presheaf.map (homOfLE hW).op (secOf L n hG N ψ' V s) = secOf L n hG N ψ' W ((L.eigenSubdatum n hG χ).res hW s) :=
  (ψ'.naturality_apply hW s).symm

theorem smul_secOf (V : A.Opens) (a : Γ(A, V)) (s : (L.eigenSubdatum n hG χ).obj V) :
    a • secOf L n hG N ψ' V s = secOf L n hG N ψ' V (a • s) :=
  (ψ'.app_smul V a s).symm

include h h' in

theorem isFrameOn_of_eigen (V : A.Opens) (s : (L.eigenSubdatum n hG χ).obj V)
    (hs : ∀ (W : A.affineOpens) (hW : W.1 ≤ V),
      Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG χ).res hW s)) :
    Scheme.Modules.IsFrameOn (secOf L n hG N ψ' V s) V := by
  apply AlgebraicGeometry.Scheme.Modules.isFrameOn_of_forall_affineOpens_bijective_smul
  intro W hW
  have e := map_secOf L n hG N ψ' hW s
  simp only [e]
  have hψ : Function.Bijective (ψ'.app W.1) :=
    Function.bijective_iff_has_inverse.2 ⟨φ.app W.1, fun x => h W.1 x, fun x => h' W.1 x⟩
  have hcomp : (fun a : Γ(A, W.1) => a • secOf L n hG N ψ' W.1 ((L.eigenSubdatum n hG χ).res hW s)) =
      (ψ'.app W.1) ∘ (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG χ).res hW s) := by
    funext a
    exact smul_secOf L n hG N ψ' W.1 a _
  rw [hcomp]
  exact hψ.comp (hs W hW)

end Frames

end Ws23ET

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R)
    (N₁ N₂ N₃ : A.Modules)
    (φ₁ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₁) (L.eigenSubdatum n hG χ))
    (ψ₁ : OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.ofModules f N₁))
    (h₁ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U), φ₁.app U (ψ₁.app U s) = s)
    (h₁' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₁).obj U), ψ₁.app U (φ₁.app U s) = s)
    (φ₂ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₂) (L.eigenSubdatum n hG ψ))
    (ψ₂ : OModulePresheaf.Hom (L.eigenSubdatum n hG ψ) (OModulePresheaf.ofModules f N₂))
    (h₂ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG ψ).obj U), φ₂.app U (ψ₂.app U s) = s)
    (h₂' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₂).obj U), ψ₂.app U (φ₂.app U s) = s)
    (φ₃ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₃) (L.eigenSubdatum n hG (χ * ψ)))
    (ψ₃ : OModulePresheaf.Hom (L.eigenSubdatum n hG (χ * ψ)) (OModulePresheaf.ofModules f N₃))
    (h₃ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG (χ * ψ)).obj U), φ₃.app U (ψ₃.app U s) = s)
    (h₃' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₃).obj U), ψ₃.app U (φ₃.app U s) = s)
    (hfr : ∀ y : A, ∃ V : A.affineOpens, y ∈ V.1 ∧
      ∃ (s : (L.eigenSubdatum n hG χ).obj V.1) (t : (L.eigenSubdatum n hG ψ).obj V.1),
        ∀ (W : A.affineOpens) (hW : W.1 ≤ V.1),
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG χ).res hW s) ∧
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG ψ).res hW t) ∧
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG (χ * ψ)).res hW (L.eigenMul n hG s t))) :
    Nonempty (N₁ ⊗ N₂ ≅ N₃) := by
  classical

  obtain ⟨ν, hν⟩ := AlgebraicGeometry.Scheme.Modules.exists_hom_tensor_app_tensorSections_eq_of_bilinear N₁ N₂ N₃
    (Ws23ET.pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃) (fun i s t => Ws23ET.map_pairing L n hG N₁ N₂ N₃ φ₁ φ₂ ψ₃ i s t)

  choose V hV s t hst using hfr
  haveI : IsIso ν := by
    refine AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2 ν (fun y : A => (V y).1) ?_
      (fun y => Scheme.Modules.tensorSections (Ws23ET.secOf L n hG N₁ ψ₁ (V y).1 (s y)) (Ws23ET.secOf L n hG N₂ ψ₂ (V y).1 (t y)))
      (fun y => Ws23ET.secOf L n hG N₃ ψ₃ (V y).1 (L.eigenMul n hG (s y) (t y))) ?_ ?_ ?_
    · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩
    · intro y
      exact AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2
        (Ws23ET.isFrameOn_of_eigen L n hG N₁ φ₁ ψ₁ h₁ h₁' (V y).1 (s y) fun W hW => (hst y W hW).1)
        (Ws23ET.isFrameOn_of_eigen L n hG N₂ φ₂ ψ₂ h₂ h₂' (V y).1 (t y) fun W hW => (hst y W hW).2.1)
    · intro y
      exact Ws23ET.isFrameOn_of_eigen L n hG N₃ φ₃ ψ₃ h₃ h₃' (V y).1 (L.eigenMul n hG (s y) (t y))
        fun W hW => (hst y W hW).2.2
    · intro y
      rw [hν, Ws23ET.pairing_apply]
      show ψ₃.app (V y).1 _ = ψ₃.app (V y).1 _
      rw [Ws23ET.secOf, Ws23ET.secOf, h₁, h₂]
  exact ⟨asIso ν⟩

end S_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul (solution)
