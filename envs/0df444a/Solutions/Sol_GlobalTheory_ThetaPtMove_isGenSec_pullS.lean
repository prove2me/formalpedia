-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.isGenSec_pullS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:37.028519+00:00
-- url     : https://prove2.me/submissions/94e4b48a-c830-4d23-b9ba-48df10ffd7a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_GlobalTheory_VVRank_isPullSec_pullS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtMove
theorem _root_.solution (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [Subsingleton S] (p : S) (P : PolAV S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) ⊤).left)
    (th : LB.Sec (LPow P.A P.L 1 (overRes (T := baseOver S) ⊤))) (h : IsGenSec P.A P.L 1 th) :
    IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t) th) := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl p
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
  obtain ⟨-, hsp⟩ := hb R t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  have hle : (⊤ : Submodule Γ((baseAt t).left, ⊤) (SecM P.A P.L 1 (baseAt t))) ≤
      Submodule.span _ {SecM.ofSec P.A (VVRank.pullS P.A 1 (homAt t) th)} := by
    refine hsp.ge.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := h (b i)
    have e : SecM.ofSec P.A (b i) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    refine Submodule.mem_span_singleton.2 ⟨(homAt t).left.appTop.hom r, ?_⟩
    exact ((VVRank.pullM P.A P.L 1 (homAt t)).map_smulₛₗ r _).symm.trans
      (congrArg (VVRank.pullM P.A P.L 1 (homAt t)) e.symm)
  intro s
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hle (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨c, fun j => (congrArg (fun q => q.1 j) hc).symm⟩
end GlobalTheory.ThetaPtMove
