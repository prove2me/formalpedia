-- Prove2me | solution 1 for GlobalTheory.CechCmp.toCech_cocycle_read
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:21:26.883829+00:00
-- url     : https://prove2.me/submissions/f9360349-d099-4490-9a4a-4b9fb6d2f3e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCocyclePosetOneCochainToCechCochain
import Theorems.Thm_GlobalTheory_CechCmp_cv_mp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_rsT_add
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} [Finite I] {X : Scheme.{0}} {R : Type} [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
namespace GlobalTheory.CechCmp
theorem _root_.solution (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf))
    (x : I) (P K : NE I) (hxP : P ≤ NE.single x) (hPK : K ≤ P) (hxK : K ≤ NE.single x)
    (W : X.Opens) (hW : W ≤ cap U K) :
    rsT (cv s U hU hinf (op P) (f (op (NE.single x)) (op P) (homOfLE hxP).op)) W =
      rsT (cv s U hU hinf (op K) (f (op (NE.single x)) (op K) (homOfLE hxK).op)) W -
        rsT (cv s U hU hinf (op K) (f (op P) (op K) (homOfLE hPK).op)) W := by
  have e := Z1.comp ⟨f, hf⟩ (homOfLE hxP).op (homOfLE hPK).op
  have hc : (homOfLE hxP).op ≫ (homOfLE hPK).op = (homOfLE hxK).op := Subsingleton.elim _ _
  rw [hc] at e
  have e' := congrArg (fun b => rsT (cv s U hU hinf (op K) b) W) e
  simp only [map_add, GlobalTheory.KS.rsT_add] at e'
  rw [cv_mp s U hU hinf (homOfLE hPK).op] at e'
  rw [GlobalTheory.KS.rsT_rsT (O₁ := cap U (op K).unop) (cap_mono U hPK) hW] at e'
  rw [e']
  abel
end GlobalTheory.CechCmp
