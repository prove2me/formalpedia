-- Prove2me | solution 1 for GlobalTheory.LocalInv.eig_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:27.694019+00:00
-- url     : https://prove2.me/submissions/c992e4a1-ec79-4566-843b-c8ae09002765

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_charRep_charpoly
import Theorems.Thm_GlobalTheory_LocalInv_isRoot_charpoly
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (eig : Eig N A) (h1 : EigAway N A eig) (h2 : EigAbove N A eig) (i : N.Loc) {a : ℕ}
    (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (χ : G H.E N.Om →* (N.O i)ˣ) (hρ : Cont N i ρ)
    (hχ : Cont N i (charRep N i χ)) (w : PlE H)
    (dρ : w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)
    (dχ : w ∈ placesOver H.E (N.l i) → DeRham N A i (charRep N i χ) w)
    (hs : SubOrQuot N i ρ χ w) (σ : G H.E N.Om) (hσ : FrobLift N w σ) (c : ℂ)
    (hc : eig w (wd N A i (charRep N i χ) w) σ = {c}) : c ∈ eig w (wd N A i ρ w) σ := by
  by_cases hw : w ∈ placesOver H.E (N.l i)
  · have := h2 i a ρ χ hρ hχ w hw (dρ hw) (dχ hw) hs σ hσ
    rw [hc] at this
    exact Multiset.singleton_le.mp this
  · have e1 := h1 i 1 _ hχ w hw σ hσ
    rw [hc, charRep_charpoly] at e1
    have hcc : iotaO N A i ((χ σ : (N.O i)ˣ) : N.O i) = c := by
      simpa using e1
    obtain ⟨v, hv, h⟩ := hs
    have hr := isRoot_charpoly (matK N i ρ σ) _ v hv (h.imp (fun h => h σ hσ.1) (fun h => h σ hσ.1))
    have hr2 := hr.map (f := (A.iotaQC i).toRingHom.comp (A.iotaQ i))
    rw [matK, Matrix.charpoly_map, Polynomial.map_map] at hr2
    have hr3 : (((ρ σ : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map
        (iotaO N A i)).IsRoot c := by
      rw [← hcc]
      exact hr2
    rw [h1 i a ρ hρ w hw σ hσ, IsRoot.def, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff,
      Multiset.map_map, Multiset.mem_map] at hr3
    obtain ⟨α, hα, h0⟩ := hr3
    have : c = α := by simpa [sub_eq_zero] using h0
    rwa [this]
end GlobalTheory.LocalInv
