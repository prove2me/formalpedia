-- Prove2me | solution 1 for OAI.SimpleFInftyOvergroups.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:03:46.495671+00:00
-- url     : https://prove2.me/submissions/853e862f-ce53-41ed-8fea-a41b1e1fb1d3

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So034
import Theorems.Thm_OAI_SimpleFInftyOvergroups_SourceRingData_realize

section
-- module Solutions.OAIQ066_SO.FiniteType_StageGeometry
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SimpleFInftyOvergroups
universe u

lemma evalWord_map {G : Type u} {H : Type*} [Group G] [Group H]
    (f : G →* H) {n : ℕ} (g : Fin n → G) (w : List (Fin n × Bool)) :
    evalWord (fun i => f (g i)) w = f (evalWord g w) := by
  simp only [evalWord,map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  split <;> simp_all

lemma wordProblem_of_equiv {G : Type u} {H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : HasDecidableWordProblem G) : HasDecidableWordProblem H := by
  obtain ⟨n,g,hg,hc⟩ := h
  refine ⟨n,(fun i => e (g i)),?_,?_⟩
  · apply top_unique
    intro y hy
    clear hy
    obtain ⟨x,rfl⟩ := e.surjective y
    have hx : x ∈ Subgroup.closure (Set.range g) := by rw [hg]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i,rfl⟩
    | one => simp
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  · have he : (fun w : List (Fin n × Bool) => evalWord (fun i => e (g i)) w = 1) =
        (fun w => evalWord g w = 1) := by
      funext w
      apply propext
      change evalWord (fun i => e.toMonoidHom (g i)) w = 1 ↔ _
      rw [evalWord_map]
      exact e.map_eq_one_iff
    rw [he]
    exact hc

lemma small_model (G : Type u) [Group G] (h : HasDecidableWordProblem G) :
    ∃ (G₀ : Type) (_ : Group G₀), Nonempty (G₀ ≃* G) ∧ HasDecidableWordProblem G₀ := by
  obtain ⟨n,g,hg,hc⟩ := h
  let p : FreeGroup (Fin n) →* G := FreeGroup.lift g
  have hp : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top]
    change (FreeGroup.lift g).range = ⊤
    apply top_unique
    rw [← hg]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨FreeGroup.of i,by simp⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  exact ⟨FreeGroup (Fin n) ⧸ p.ker,inferInstance,⟨e⟩,
    wordProblem_of_equiv e.symm ⟨n,g,hg,hc⟩⟩
end SimpleFInftyOvergroups

namespace CWUniverse
open Set Topology
universe u
variable {X : Type} [TopologicalSpace X] [CWComplex (univ : Set X)]

lemma finiteType [Topology.CWComplex.FiniteType (univ : Set X)] :
    letI := cw.{u} (X:=X)
    Topology.CWComplex.FiniteType (univ : Set (ULift.{u} X)) := by
  let := cw.{u} (X:=X)
  refine ⟨fun n => ?_⟩
  change Finite (ULift.{u} (Topology.CWComplex.cell (univ : Set X) n))
  let : Finite (Topology.CWComplex.cell (univ : Set X) n) :=
    Topology.CWComplex.FiniteType.finite_cell (C:=(univ : Set X)) (D:=∅) n
  infer_instance

end CWUniverse

namespace SimpleFInftyOvergroups
universe u
lemma HasTypeFInfty.ulift {H : Type} [Group H] (h : HasTypeFInfty H) :
    HasTypeFInfty (ULift.{u} H) := by
  obtain ⟨X,t,cw,ht,hc,hf,x,⟨e⟩,E,tE,p,hp,hs,hE⟩ := h
  let := t
  let := tE
  let := cw
  let := ht
  let := hc
  let := hf
  let := hE
  let := CWUniverse.cw.{u} (X:=X)
  let : ContractibleSpace (ULift.{u} E) := Homeomorph.ulift.contractibleSpace
  refine ⟨ULift.{u} X,inferInstance,inferInstance,inferInstance,?_,
    CWUniverse.finiteType,ULift.up x,⟨MulEquiv.ulift.trans (e.trans (CWUniverse.piOne x))⟩,
    ULift.{u} E,inferInstance,ULift.up ∘ p ∘ ULift.down,?_,?_,inferInstance⟩
  · exact Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  · exact (hp.comp_homeomorph Homeomorph.ulift).homeomorph_comp Homeomorph.ulift.symm
  · exact ULift.up_surjective.comp (hs.comp ULift.down_surjective)

lemma lift_explicit_overgroup {G : Type u} [Group G] {G₀ H : Type} [Group G₀] [Group H]
    (e : G₀ ≃* G) (f : G₀ →* H) (hinj : Function.Injective f)
    (hnt : Nontrivial H) (hsi : IsSimpleGroup H) (hf : HasTypeFInfty H) :
    Nontrivial (ULift.{u} H) ∧ IsSimpleGroup (ULift.{u} H) ∧
      HasTypeFInfty (ULift.{u} H) ∧
        ∃ f' : G →* ULift.{u} H, Function.Injective f' := by
  let := hnt
  let := hsi
  refine ⟨inferInstance,MulEquiv.ulift.isSimpleGroup,hf.ulift,?_,?_⟩
  · exact MulEquiv.ulift.symm.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  · exact MulEquiv.ulift.symm.injective.comp (hinj.comp e.symm.injective)
end SimpleFInftyOvergroups

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceRingReduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups
open StageConstruction SourceEnlargement
open scoped Classical

universe u

theorem main_of_sourceRingProducer (produce : SourceRingProducerObligation)
    (G : Type u) [Group G] [Group.FG G] (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  obtain ⟨G₀, i₀, ⟨e⟩, h₀⟩ := small_model G hG
  let _ := i₀
  obtain ⟨d⟩ := produce G₀ h₀
  obtain ⟨H, iH, hnt, hsi, hf, f, hinj⟩ := d.realize
  let _ := iH
  exact ⟨ULift.{u} H, inferInstance, lift_explicit_overgroup e f hinj hnt hsi hf⟩

end SimpleFInftyOvergroups
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups

theorem sourceRingProducer : SourceRingProducerObligation := by
  intro G _ hG
  obtain ⟨k,s,hs,hw⟩ := hG
  exact ⟨SourceModel.data s hw hs⟩

universe u

theorem main_oai (G : Type u) [Group G] [Group.FG G] (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f :=
  main_of_sourceRingProducer sourceRingProducer G hG

end SimpleFInftyOvergroups
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SimpleFInftyOvergroups.main_oai.{u} := @OAI.SimpleFInftyOvergroups.main_oai.{u}
