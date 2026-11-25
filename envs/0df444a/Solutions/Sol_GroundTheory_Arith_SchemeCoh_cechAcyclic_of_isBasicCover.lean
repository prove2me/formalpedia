-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechAcyclic_of_isBasicCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:08.591102+00:00
-- url     : https://prove2.me/submissions/9beb3a98-92d7-4a69-adc1-f27114f0a879

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_of_transport
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_image_inter
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_retract
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechCondition_tilde


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    {κ : Type u} [Finite κ] {U : κ → X.Opens} (hU : IsBasicCover V U) :
    CechAcyclic (modulesAb F).obj U := by
  obtain ⟨hV, h, hUh, hsup⟩ := hU
  have hUeq : U = fun a => X.basicOpen (h a) := funext hUh
  subst hUeq
  let F' : (Spec Γ(X, V)).Modules := F.restrict hV.fromSpec
  let M := (modulesSpecToSheaf.obj F').presheaf.obj (op ⊤)
  let U' : κ → Opens (Spec Γ(X, V)).toTopCat := fun a => PrimeSpectrum.basicOpen (h a)
  have hsup' : iSup U' = ⊤ := by
    have h1 : hV.fromSpec ⁻¹ᵁ (⨆ a, X.basicOpen (h a)) = ⊤ := by
      rw [hsup]
      exact hV.fromSpec_preimage_self
    rw [Scheme.Hom.preimage_iSup] at h1
    simpa only [hV.fromSpec_preimage_basicOpen] using h1
  have hM : CechAcyclic (tildeAb M).obj U' :=
    cechCondition_tilde M ⊤ ⟨1, PrimeSpectrum.basicOpen_one.symm⟩ κ U' (fun a => ⟨h a, rfl⟩)
      hsup'
  have : F'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor hV.fromSpec F
  have hiso : IsIso F'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F'
  let e : tildeAb M ≅ modulesAb F' :=
    (SheafOfModules.toSheaf _).mapIso (@asIso _ _ _ _ F'.fromTildeΓ hiso)
  have hF' : CechAcyclic (modulesAb F').obj U' :=
    CechAcyclic.of_retract U' e.inv.hom e.hom.hom (congrArg (fun f => f.hom) e.inv_hom_id) hM
  have key := cechAcyclic_of_transport (P := (modulesAb F).obj) (P' := (modulesAb F').obj)
    (fun W => hV.fromSpec ''ᵁ W) (fun _ _ hle => hV.fromSpec.image_mono hle)
    (fun W => AddEquiv.refl _) (fun _ _ => rfl) U' (fun i => image_inter hV.fromSpec U' i) hF'
  convert key using 1
  funext a
  exact (hV.fromSpec_image_basicOpen (h a)).symm
end GroundTheory.Arith.SchemeCoh
