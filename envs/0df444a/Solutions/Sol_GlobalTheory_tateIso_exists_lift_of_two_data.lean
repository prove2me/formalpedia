-- Prove2me | solution 1 for GlobalTheory.tateIso_exists_lift_of_two_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:04.523462+00:00
-- url     : https://prove2.me/submissions/dc6b7fae-fde7-496a-ad14-e0ec472058bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TateIsoExistsLiftOfTwoData
import Theorems.Thm_GlobalTheory_tateIso_ev_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory
theorem _root_.solution (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  let R : Submodule (𝓞 E) (D.La × D'.La) :=
    { carrier := {p | I.ev n p.1 = I'.ev n p.2}
      add_mem' := fun {p q} hp hq => by
        change I.ev n (p.1 + q.1) = I'.ev n (p.2 + q.2)
        rw [I.add, I'.add, show I.ev n p.1 = I'.ev n p.2 from hp, show I.ev n q.1 = I'.ev n q.2 from hq]
      zero_mem' := by
        change I.ev n 0 = I'.ev n 0
        rw [(I.ker n hn 0).2 ⟨0, by simp⟩, (I'.ker n hn 0).2 ⟨0, by simp⟩]
      smul_mem' := fun c p hp => by
        change I.ev n (c • p.1) = I'.ev n (c • p.2)
        rw [I.lin, I'.lin, show I.ev n p.1 = I'.ev n p.2 from hp] }
  have hs : Function.Surjective ((LinearMap.fst (𝓞 E) D.La D'.La).comp R.subtype) := fun a => by
    obtain ⟨b, hb⟩ := (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  haveI := D.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  refine ⟨((LinearMap.snd (𝓞 E) D.La D'.La).comp R.subtype).comp s, fun a => ?_⟩
  have h1 : (s a).1.1 = a := LinearMap.congr_fun hs a
  have h2 : I.ev n (s a).1.1 = I'.ev n (s a).1.2 := (s a).2
  rw [h1] at h2
  exact h2
end GlobalTheory
