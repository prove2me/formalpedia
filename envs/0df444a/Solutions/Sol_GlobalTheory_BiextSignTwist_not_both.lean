-- Prove2me | solution 1 for GlobalTheory.BiextSignTwist.not_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:28.455492+00:00
-- url     : https://prove2.me/submissions/9ed08a9a-963c-4586-8593-0ab9c48648a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BiextSignTwist
variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.BiextSignTwist
theorem _root_.solution (h2 : IsUnit (2 : Γ(S, ⊤))) [Nonempty S] (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) (h : LawIsCube G L c ψ law) :
    ¬ LawIsCube G L c ψ (negGen law) := by
  intro h'
  obtain ⟨s⟩ : Nonempty S := inferInstance
  let e : 𝟙_ (Over S) ⟶ G3 G := lift η[G] (lift η[G] η[G])
  let z : (G3 G).left := e.left s
  have hc : ∀ x : G.left, ∃ i, x ∈ L.L.U i := fun x => by
    have : x ∈ (⨆ i, L.L.U i) := by rw [L.isLB.cover]; trivial
    exact Opens.mem_iSup.1 this
  choose idx hidx using hc
  let J : ULift.{u} (Fin 3) → ULift.{u} (Finset (Fin 2)) → L.L.ι :=
    fun k I => idx ((ψ k ≫ lamφ G I) z)
  let j : thK → L.L.ι := fun I => idx ((thφ G (x3 G) I) z)
  have a1 : ∀ k I k' I', ψ k ≫ lamφ G I = ψ k' ≫ lamφ G I' → J k I = J k' I' :=
    fun k I k' I' e => by simp only [J, e]
  have a2 : LB.Coh L.L (thφ G (x3 G)) j := fun I I' e => by simp only [j, e]
  have a3 : ∀ k I I', ψ k ≫ lamφ G I = thφ G (x3 G) I' → J k I = j I' :=
    fun k I I' e => by simp only [J, j, e]
  have e1 := h J j a1 a2 a3
  have e2 := h' J j a1 a2 a3
  rw [← e1] at e2
  replace e2 := (res_neg _ _).symm.trans e2
  set W := LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j with hW
  have hz : z ∈ W := by
    refine ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun I => ?_, Set.mem_iInter.2 fun I => hidx _⟩
    have := hidx ((ψ k ≫ lamφ G I) z)
    rw [Scheme.Hom.comp_apply] at this
    exact this
  haveI : Nonempty W := ⟨⟨z, hz⟩⟩
  have h2' : IsUnit (2 : Γ((G3 G).left, W)) := by
    have := (h2.map ((G3 G).hom.appTop).hom).map
      ((G3 G).left.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
    simpa only [map_ofNat] using this
  have key : ∀ a : Γ((G3 G).left, W)ˣ, -a = a → False := fun a e2 => by
    have e3 : (2 : Γ((G3 G).left, W)) * (a : Γ((G3 G).left, W)) = 0 := by
      have := congrArg Units.val e2
      rw [Units.val_neg] at this
      linear_combination -this
    exact (h2'.mul a.isUnit).ne_zero e3
  exact key _ e2
end GlobalTheory.BiextSignTwist
