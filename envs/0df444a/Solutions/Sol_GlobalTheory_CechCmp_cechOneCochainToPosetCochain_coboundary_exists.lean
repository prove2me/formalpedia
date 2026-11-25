-- Prove2me | solution 1 for GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:17.435376+00:00
-- url     : https://prove2.me/submissions/5c1ae92d-672d-4039-a2a7-8a68ad56d5fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechOneCochainToPosetCochainCoboundaryExists
import Theorems.Thm_GlobalTheory_CechCmp_NE_pt_mem
import Theorems.Thm_GlobalTheory_CechCmp_cap_le
import Theorems.Thm_GlobalTheory_CechCmp_cv_mp
import Theorems.Thm_GlobalTheory_CechCmp_cv_toPos
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_rsT_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
open GlobalTheory GlobalTheory.CechCmp
namespace GlobalTheory.CechCmp
theorem _root_.solution : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']
end GlobalTheory.CechCmp
