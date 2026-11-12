-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixMembershipName_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:30:09.875432+00:00
-- url     : https://prove2.me/submissions/74b9383a-dcb6-4966-b3c7-4e44cbceb7e0

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P011

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

theorem eval_rename (t : Presentation Q) (f : P → Q) (H : Set Q) (τ : Name s) :
    eval H (rename t f τ) = eval {p | f p ∈ H} τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro x
    rw [mem_eval, mem_eval]
    constructor
    · rintro ⟨ν, q, h, hq, eq⟩
      obtain ⟨σ, p, hp, rfl, rfl⟩ := (entry_rename t f τ ν q).1 h
      exact ⟨σ, p, hp, hq, (ih σ p hp).symm.trans eq⟩
    · rintro ⟨σ, p, hp, hq, eq⟩
      exact ⟨rename t f σ, f p,
        (entry_rename t f τ _ _).2 ⟨σ, p, hp, rfl, rfl⟩,
        hq, (ih σ p hp).trans eq⟩

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameRenameSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryMembershipDecisionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ci oi pi si ti : Fin n) (env : Fin n → ZFSet.{u})
    (sigma tau : (M.nameDomain s).names) (p : P)
    (hc : env ci = s.carrier) (ho : env oi = s.conditionOrder)
    (hp : env pi = s.encode p) (hs : env si = sigma.val.val) (ht : env ti = tau.val.val) :
    Realize M.sets (ordinaryMembershipDecisionFormula ci oi pi si ti) env ↔
      Name.ForcesMem p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesMem q sigma.val tau.val := by
  rw [ordinaryMembershipDecisionFormula, realize_disj]
  let names : Assignment (M.nameDomain s) 2 := extend sigma (extend tau Fin.elim0)
  have meaning (phi : SetFormula 2) := M.realize_ordinaryGroundForcing s pairing unions powers
    separation collection carrier order (0 : Fin 2) 1 phi (extend ci (extend oi Fin.elim0)) pi
    (extend si (extend ti Fin.elim0)) env hc ho p names hp
    (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i)))
  exact or_congr (meaning (.mem 0 1)) (meaning (.neg (.mem 0 1)))

theorem ordinaryMembershipDecisions_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) (p : P) :
    s.encode p ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma.val.val tau.val.val ↔
      Name.ForcesMem p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesMem q sigma.val tau.val := by
  rw [ordinaryMembershipDecisions, ZFSet.mem_sep, and_iff_right (s.encode_mem p)]
  exact M.realize_ordinaryMembershipDecisionFormula s pairing unions powers separation collection
    carrier order 1 2 0 3 4 _ sigma tau p rfl rfl rfl rfl rfl

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CrossStageMembershipFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower) (inclusion : Lower → Upper)

theorem realize_crossStageMembershipEntryFormula
    (unchanged : ∀ p, s.encode (inclusion p) = t.encode p)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (upperGround : s.carrier ∈ M.sets) (upperOrderGround : s.conditionOrder ∈ M.sets)
    (lowerGround : t.carrier ∈ M.sets)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ u ∈ J, IsName t u)
    (tau : Name s) (hTau : tau.val ∈ M.sets)
    {n : Nat} (zi ji li ui oi ti : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env zi ∈ M.sets) (hj : env ji = J) (hl : env li = t.carrier)
    (hu : env ui = s.carrier) (ho : env oi = s.conditionOrder) (ht : env ti = tau.val) :
    Realize M.sets (crossStageMembershipEntryFormula zi ji li ui oi ti) env ↔
      ∃ sigma : Name t, sigma.val ∈ J ∧ ∃ p : Lower,
        env zi = ZFSet.pair sigma.val (t.encode p) ∧
          Name.ForcesMem (inclusion p) (Name.rename s inclusion sigma) tau := by
  rw [crossStageMembershipEntryFormula, exConditions, realize_ex]
  constructor
  · rintro ⟨u, uGround, member, body⟩
    change u ∈ env ji at member
    rw [hj] at member
    let sigma : Name t := ⟨u, valid u member⟩
    obtain ⟨p, shape, forced⟩ :=
      (M.realize_exConditions t li.succ _ (extend u env) lowerGround hl).1 body
    have hp := M.transitive lowerGround (t.encode_mem p)
    have code := Name.rename_val_of_encode s inclusion unchanged sigma
    have liftGround : (Name.rename s inclusion sigma).val ∈ M.sets := code.symm ▸ uGround
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.rename s inclusion sigma, liftGround⟩ (extend ⟨tau, hTau⟩ Fin.elim0)
    have pair := (M.realize_orderedPairFormula pairing zi.succ.succ 1 0
      (extend (t.encode p) (extend u env)) hz uGround hp).1 shape
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      upperGround upperOrderGround (0 : Fin 2) 1 (.mem 0 1)
      (extend ui.succ.succ (extend oi.succ.succ Fin.elim0)) 0
      (extend 1 (extend ti.succ.succ Fin.elim0)) _ hu ho (inclusion p) names (unchanged p).symm
      (Fin.cases code.symm (Fin.cases ht (fun i => Fin.elim0 i)))).1 forced
    exact ⟨sigma, member, p, pair, atom⟩
  · rintro ⟨sigma, member, p, pair, forced⟩
    have hs := M.transitive hJ member
    have hp := M.transitive lowerGround (t.encode_mem p)
    have code := Name.rename_val_of_encode s inclusion unchanged sigma
    have liftGround : (Name.rename s inclusion sigma).val ∈ M.sets := code.symm ▸ hs
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.rename s inclusion sigma, liftGround⟩ (extend ⟨tau, hTau⟩ Fin.elim0)
    refine ⟨sigma.val, hs, ?_, ?_⟩
    · change sigma.val ∈ env ji
      exact hj.symm ▸ member
    · apply (M.realize_exConditions t li.succ _ (extend sigma.val env) lowerGround hl).2
      refine ⟨p, ?_, ?_⟩
      · exact (M.realize_orderedPairFormula pairing zi.succ.succ 1 0
          (extend (t.encode p) (extend sigma.val env)) hz hs hp).2 pair
      · exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
          upperGround upperOrderGround (0 : Fin 2) 1 (.mem 0 1)
          (extend ui.succ.succ (extend oi.succ.succ Fin.elim0)) 0
          (extend 1 (extend ti.succ.succ Fin.elim0)) _ hu ho (inclusion p) names (unchanged p).symm
          (Fin.cases code.symm (Fin.cases ht (fun i => Fin.elim0 i)))).2 forced

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionGenericity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem codedFamily_of_code {E : Set P} (code : s.subset E ∈ M.sets) : E ∈ M.codedFamily s := by
  refine ⟨s.subset E, code, ?_⟩
  apply Set.ext
  intro p
  exact s.encode_mem_subset E p

theorem generic_meets_coded_dense [Preorder P] (H : ConditionFilter P)
    (generic : H.GenericFor (M.codedFamily s)) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E :=
  generic E (M.codedFamily_of_code s code) dense

end TransitiveGround



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u}) (tau : Name s)

theorem pair_mem_crossStageMembershipCode (sigma : Name t) (p : Lower) :
    ZFSet.pair sigma.val (t.encode p) ∈ crossStageMembershipCode s t inclusion J tau ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau := by
  change (_ ∈ ZFSet.sep _ _) ↔ _
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, nu, q, equal, forced⟩
    obtain ⟨names, conditions⟩ := ZFSet.pair_inj.1 equal
    have sameName : sigma = nu := Subtype.ext names
    have sameCondition : p = q := t.injective conditions
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, sameName.symm ▸ sameCondition.symm ▸ forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨member, t.encode_mem p⟩, sigma, p, rfl, forced⟩

theorem entry_crossStageMembershipName (valid : ∀ z ∈ J, IsName t z)
    (sigma : Name t) (p : Lower) :
    Entry sigma (crossStageMembershipName s t inclusion J valid tau) p ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau :=
  pair_mem_crossStageMembershipCode s t inclusion J tau sigma p

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower) (inclusion : Lower → Upper)
variable (unchanged : ∀ p, s.encode (inclusion p) = t.encode p)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (upperGround : s.carrier ∈ M.sets) (upperOrderGround : s.conditionOrder ∈ M.sets)
variable (lowerGround : t.carrier ∈ M.sets)
variable {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ u ∈ J, IsName t u)
variable (tau : Name s) (hTau : tau.val ∈ M.sets)
include unchanged pairing unions powers separation collection upperGround upperOrderGround lowerGround hJ valid hTau

theorem crossStageMembershipCode_eq_selection :
    Name.crossStageMembershipCode s t inclusion J tau =
      ZFSet.sep (fun z => Realize M.sets (crossStageMembershipEntryFormula 0 1 2 3 4 5)
        (extend z ![J, t.carrier, s.carrier, s.conditionOrder, tau.val])) (ZFSet.prod J t.carrier) := by
  have productGround := M.prod_mem pairing unions powers separation hJ lowerGround
  have recognize (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (crossStageMembershipEntryFormula 0 1 2 3 4 5)
        (extend z ![J, t.carrier, s.carrier, s.conditionOrder, tau.val]) ↔
      z ∈ Name.crossStageMembershipCode s t inclusion J tau := by
    rw [M.realize_crossStageMembershipEntryFormula s t inclusion unchanged
      pairing unions powers separation collection upperGround upperOrderGround lowerGround hJ valid tau hTau
      0 1 2 3 4 5 _ hz rfl rfl rfl rfl rfl]
    constructor
    · rintro ⟨sigma, member, p, rfl, forced⟩
      exact (Name.pair_mem_crossStageMembershipCode s t inclusion J tau sigma p).2 ⟨member, forced⟩
    · intro member
      obtain ⟨bound, sigma, p, rfl, forced⟩ := ZFSet.mem_sep.1 member
      exact ⟨sigma, (ZFSet.pair_mem_prod.1 bound).1, p, rfl, forced⟩
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    have bound := Name.crossStageMembershipCode_subset s t inclusion J tau member
    exact ⟨bound, (recognize z (M.transitive productGround bound)).2 member⟩
  · rintro ⟨bound, formula⟩
    exact (recognize z (M.transitive productGround bound)).1 formula

theorem crossStageMembershipCode_mem :
    Name.crossStageMembershipCode s t inclusion J tau ∈ M.sets := by
  rw [M.crossStageMembershipCode_eq_selection s t inclusion unchanged pairing unions powers
    separation collection upperGround upperOrderGround lowerGround hJ valid tau hTau]
  exact M.separation_mem separation (crossStageMembershipEntryFormula 0 1 2 3 4 5)
    ![J, t.carrier, s.carrier, s.conditionOrder, tau.val]
    (Fin.cases hJ (Fin.cases lowerGround (Fin.cases upperGround
      (Fin.cases upperOrderGround (Fin.cases hTau (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hJ lowerGround)

theorem crossStageMembershipName_mem :
    (Name.crossStageMembershipName s t inclusion J valid tau).val ∈ M.sets :=
  M.crossStageMembershipCode_mem s t inclusion unchanged pairing unions powers separation collection
    upperGround upperOrderGround lowerGround hJ valid tau hTau

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPredenseMeet
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)

theorem generic_meets_ground_predense (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (M.codedFamily s))
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (subset : A ⊆ s.carrier)
    (predense : ∀ q ∈ s.carrier, ∃ p ∈ A, ∃ r ∈ s.carrier,
      ZFSet.pair r q ∈ s.conditionOrder ∧ ZFSet.pair r p ∈ s.conditionOrder) :
    ∃ p : P, H.mem p ∧ s.encode p ∈ A := by
  let E : Set P := {r | ∃ p ∈ A, ZFSet.pair (s.encode r) p ∈ s.conditionOrder}
  let raw := ZFSet.sep (fun r => ∃ p ∈ A, ZFSet.pair r p ∈ s.conditionOrder) s.carrier
  let formula : BoundedFormula 3 :=
    BoundedFormula.exMem 1 (BoundedFormula.pairMembershipFormula 1 0 3)
  let params := extend A (extend s.conditionOrder Fin.elim0)
  have selected := M.bounded_separation_mem separation formula params
    (Fin.cases hA (Fin.cases order (fun j => Fin.elim0 j))) carrier
  have rawGround : raw ∈ M.sets := by
    have equal : ZFSet.sep (fun r => BoundedFormula.Truth formula (extend r params)) s.carrier = raw := by
      apply ZFSet.ext
      intro r
      rw [ZFSet.mem_sep, ZFSet.mem_sep]
      apply and_congr_right
      intro _
      simp only [formula, BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
      rfl
    exact equal ▸ selected
  have code : s.subset (fun condition => condition ∈ E) = raw := by
    apply ZFSet.ext
    intro z
    rw [s.mem_subset, ZFSet.mem_sep]
    constructor
    · rintro ⟨r, member, rfl⟩
      exact ⟨s.encode_mem r, member⟩
    · rintro ⟨member, entry⟩
      obtain ⟨r, rfl⟩ := (s.mem_carrier z).1 member
      exact ⟨r, entry, rfl⟩
  have dense : Dense E := by
    intro q
    obtain ⟨p, hp, r, hr, rq, rp⟩ := predense (s.encode q) (s.encode_mem q)
    obtain ⟨r, rfl⟩ := (s.mem_carrier r).1 hr
    exact ⟨r, (s.pair_mem_conditionOrder r q).1 rq, p, hp, rp⟩
  obtain ⟨r, member, p, hp, below⟩ :=
    M.generic_meets_coded_dense s H generic (code.symm ▸ rawGround) dense
  obtain ⟨p, rfl⟩ := (s.mem_carrier p).1 (subset hp)
  exact ⟨p, H.upward member ((s.pair_mem_conditionOrder r p).1 below), hp⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u})
variable (valid : ∀ z ∈ J, IsName t z) (D : NameDomain s) (tau : Name s)
variable (H : ConditionFilter Upper) (generic : H.GenericFor (atomicFamily D))
variable (target : tau ∈ D.names)
variable (terms : ∀ sigma : Name t, sigma.val ∈ J → rename s inclusion sigma ∈ D.names)
variable (one : Lower) (hone : H.mem (inclusion one))
variable (decisions : ∀ sigma : Name t, sigma.val ∈ J → ∃ p : Lower,
  H.mem (inclusion p) ∧
    (ForcesMem (inclusion p) (rename s inclusion sigma) tau ∨
      ∀ q, q ≤ inclusion p → ¬ ForcesMem q (rename s inclusion sigma) tau))

include generic target terms hone decisions

theorem eval_crossStageMembershipName_of_decisions :
    eval {p | H.mem (inclusion p)} (crossStageMembershipName s t inclusion J valid tau) =
      eval {p | H.mem p} tau ∩
        eval {p | H.mem (inclusion p)} (familySet one J valid) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro member
    obtain ⟨sigma, p, entry, hp, value⟩ := (mem_eval _ _ x).1 member
    obtain ⟨inJ, forced⟩ := (entry_crossStageMembershipName s t inclusion J tau valid sigma p).1 entry
    have sound := forcesMem_sound D H generic (terms sigma inJ) target hp forced
    rw [eval_rename] at sound
    change eval {p | H.mem (inclusion p)} sigma ∈ eval {p | H.mem p} tau at sound
    refine ZFSet.mem_inter.2 ⟨value ▸ sound, ?_⟩
    exact (mem_eval_familySet _ one hone J valid x).2 ⟨sigma, inJ, value⟩
  · intro member
    obtain ⟨inTau, inFamily⟩ := ZFSet.mem_inter.1 member
    obtain ⟨sigma, inJ, value⟩ := (mem_eval_familySet _ one hone J valid x).1 inFamily
    have upperMember : eval {p | H.mem p} (rename s inclusion sigma) ∈
        eval {p | H.mem p} tau := by
      rw [eval_rename]
      change eval {p | H.mem (inclusion p)} sigma ∈ eval {p | H.mem p} tau
      exact value.symm ▸ inTau
    obtain ⟨p, hp, positive | negative⟩ := decisions sigma inJ
    · exact (mem_eval _ _ x).2 ⟨sigma, p,
        (entry_crossStageMembershipName s t inclusion J tau valid sigma p).2 ⟨inJ, positive⟩,
        hp, value⟩
    · obtain ⟨q, hq, forced⟩ :=
        (eval_mem_iff_forcesMem D H generic (terms sigma inJ) target).1 upperMember
      obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
      exact False.elim (negative r rp (forcesMem_mono forced rq))

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Upper Lower : Type u}
variable [PartialOrder Upper] [PartialOrder Lower] [OrderTop Lower]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (restriction : Upper →o Lower) (inclusion : Lower ↪o Upper)
variable (projection : CompleteProjection restriction inclusion)
variable (codes : ∀ p, s.encode (inclusion p) = t.encode p)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (upperCarrier : s.carrier ∈ M.sets) (upperOrder : s.conditionOrder ∈ M.sets)
variable (lowerCarrier : t.carrier ∈ M.sets) (lowerOrder : t.conditionOrder ∈ M.sets)
variable {J f : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName t z)
variable (tau : (M.nameDomain s).names)
variable (function : ZFSet.IsFunc J (M.groundPower s.carrier) f)
variable (selected : ∀ sigma A, ZFSet.pair sigma A ∈ f →
  A ⊆ M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma tau.val.val ∧
    A ⊆ t.carrier ∧ ∀ q ∈ t.carrier, ∃ p ∈ A, ∃ r ∈ t.carrier,
      ZFSet.pair r q ∈ t.conditionOrder ∧ ZFSet.pair r p ∈ t.conditionOrder)
variable (H : ConditionFilter Upper)
variable (upperGeneric : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (lowerGeneric : (projection.projectedFilter H).GenericFor (M.codedFamily t))
include codes pairing unions powers separation collection upperCarrier upperOrder lowerCarrier lowerOrder
  hJ function selected upperGeneric lowerGeneric

theorem crossStageMembershipName_eval_of_family :
    Name.eval {p | (projection.projectedFilter H).mem p}
      (Name.crossStageMembershipName s t inclusion J valid tau.val) =
      Name.eval {p | H.mem p} tau.val ∩
        Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) := by
  have terms (sigma : Name t) (member : sigma.val ∈ J) :
      Name.rename s inclusion sigma ∈ (M.nameDomain s).names := by
    change (Name.rename s inclusion sigma).val ∈ M.sets
    rw [Name.rename_val_of_encode s inclusion codes]
    exact M.transitive hJ member
  have decisions (sigma : Name t) (member : sigma.val ∈ J) : ∃ p : Lower,
      H.mem (inclusion p) ∧
        (Name.ForcesMem (inclusion p) (Name.rename s inclusion sigma) tau.val ∨
          ∀ q, q ≤ inclusion p → ¬ Name.ForcesMem q (Name.rename s inclusion sigma) tau.val) := by
    obtain ⟨A, entry, _⟩ := function.2 sigma.val member
    have groundA := ((M.mem_groundPower s.carrier A).1
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2).1
    obtain ⟨domain, bound, predense⟩ := selected sigma.val A entry
    obtain ⟨p, hp, inA⟩ := M.generic_meets_ground_predense t separation lowerCarrier lowerOrder
      (projection.projectedFilter H) lowerGeneric groundA bound predense
    let upperSigma : (M.nameDomain s).names := ⟨Name.rename s inclusion sigma, terms sigma member⟩
    have decisionEntry : s.encode (inclusion p) ∈
        M.ordinaryMembershipDecisions s.carrier s.conditionOrder upperSigma.val.val tau.val.val := by
      change s.encode (inclusion p) ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder
        (Name.rename s inclusion sigma).val tau.val.val
      rw [codes p, Name.rename_val_of_encode s inclusion codes]
      exact domain inA
    exact ⟨p, hp, (M.ordinaryMembershipDecisions_entry s pairing unions powers separation collection
      upperCarrier upperOrder upperSigma tau (inclusion p)).1 decisionEntry⟩
  have topMember : H.mem (inclusion ⊤) := by
    obtain ⟨p, hp⟩ := (projection.projectedFilter H).nonempty
    exact (projection.projectedFilter H).upward hp le_top
  have atomicGeneric : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E member dense => upperGeneric E (Or.inl member) dense
  exact Name.eval_crossStageMembershipName_of_decisions s t inclusion J valid (M.nameDomain s)
    tau.val H atomicGeneric tau.property terms ⊤ topMember decisions

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralFamilyEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
include hs hh ordinal trace hAlpha cutOrdinal subset
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace
local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed
  T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
  nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
  symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralPrefixMembershipName_eval_oai (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    let valid := (termData n).2 alpha cutOrdinal subset
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    ∀ (tau : (M.nameDomain upper).names) (f : ZFSet.{u}),
      ZFSet.IsFunc J (M.groundPower Q) f →
      (∀ sigma A, ZFSet.pair sigma A ∈ f →
        A ⊆ M.ordinaryMembershipDecisions Q
          (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) sigma tau.val.val ∧
        A ⊆ LQ ∧ ∀ q ∈ LQ, ∃ p ∈ A, ∃ r ∈ LQ,
          ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed) ∧
          ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed)) →
      let N := Name.crossStageMembershipName upper lower inc J valid tau.val
      N.val ∈ M.sets ∧ ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        ((projection).projectedFilter H).GenericFor (M.codedFamily lower) →
        Name.eval {p | ((projection).projectedFilter H).mem p} N =
          Name.eval {p | H.mem p} tau.val ∩
            Name.eval {p | ((projection).projectedFilter H).mem p} (Name.familySet ⊤ J valid) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
  let valid := (termData n).2 alpha cutOrdinal subset
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  have unchanged : ∀ p : SetMembers LQ, upper.encode (inc p) = lower.encode p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have hRestricted := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hLQ : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha hRestricted omega
  have upperOrder : upper.conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have lowerOrder : lower.conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed) :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have hUpperOrder : upper.conditionOrder ∈ M.sets := by
    rw [upperOrder]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have hLowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [lowerOrder]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha hRestricted omega
  dsimp only
  intro tau f function selected
  refine ⟨M.crossStageMembershipName_mem upper lower inc unchanged pairing unions powers separation
    collection hQ hUpperOrder hLQ (termData n).1 valid tau.val tau.property, ?_⟩
  intro H generic lowerGeneric
  apply M.crossStageMembershipName_eval_of_family upper lower
    ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code)
    ((run).inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code)
    projection unchanged pairing unions powers separation collection hQ hUpperOrder hLQ hLowerOrder
    (termData n).1 valid tau function ?_ H generic lowerGeneric
  intro sigma A entry
  rw [upperOrder, lowerOrder]
  exact selected sigma A entry

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixMembershipName_eval_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixMembershipName_eval_oai.{u}
