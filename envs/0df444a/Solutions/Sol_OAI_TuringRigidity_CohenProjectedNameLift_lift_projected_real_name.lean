-- Prove2me | solution 1 for OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:59:39.015958+00:00
-- url     : https://prove2.me/submissions/85c2a92a-5d8a-4a16-b235-485a860f0f48

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_CohenNiceNameConstruction_internal_nice_name

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenRestriction
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohen (alphabet)

theorem restrict_eq_self (B p : ZFSet.{0}) (hp : p ∈ conditions B) : restrict B p = p := by
  have hsub := ((mem_finiteSubsets_iff _ _).mp ((mem_conditions B p).mp hp).1).1
  apply ZFSet.ext; intro z
  rw [mem_restrict]
  exact ⟨And.left,fun hz => ⟨hz,hsub hz⟩⟩

theorem restrictionFormula_spec (B V p q : ℕ) (e : ℕ → ZFSet.{0}) (hV : e V = alphabet) :
    (restrictionFormula B V p q).Eval e ↔ e q = restrict (e B) (e p) := by
  simp only [restrictionFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,hV]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro z
    exact ⟨fun hz => ZFSet.mem_sep.mpr ⟨hsub hz,(h z (hsub hz)).mp hz⟩,
      fun hz => (h z (ZFSet.mem_sep.mp hz).1).mpr (ZFSet.mem_sep.mp hz).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hz => (ZFSet.mem_sep.mp hz).1,
      fun z hz => ZFSet.mem_sep.trans (and_iff_right hz)⟩

theorem pair_restrictionGraph (A B p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ restrictionGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ q = restrict B p := by
  simp only [restrictionGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,hr⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,hr⟩
  · rintro ⟨hp,hq,hr⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,hr⟩

theorem restrictionGraph_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : restrictionGraph A B ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons B (fun _ => alphabet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hcA; exact hcB; exact hB; exact InternalCohen.alphabet_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (restrictionFormula 5 6 1 0)))) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)
  have hs (z p q : ZFSet.{0}) :=
    restrictionFormula_spec 5 6 1 0 (cons q (cons p (cons z e))) rfl
  simpa only [restrictionGraph,Formula.Eval,Formula.eval_orderedPair,
    hs,cons_zero,cons_succ,e] using hh

end TuringRigidity.InternalCohenRestriction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenProjectedGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem mem_projected (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (q : Conditions (conditions B)) :
    q ∈ (projected A B hBA G).carrier ↔ ∃ p ∈ G.carrier, project A B hBA p = q := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨(factorIso A B hBA).symm (q,r),hr,?_⟩
    exact congrArg Prod.fst ((factorIso A B hBA).apply_symm_apply (q,r))
  · rintro ⟨p,hp,rfl⟩
    refine ⟨(factorIso A B hBA p).2,?_⟩
    change (factorIso A B hBA).symm (factorIso A B hBA p) ∈ G.carrier
    simpa using hp

theorem densePreimage_mem (M A B D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hD : D ∈ M) : densePreimage A B D ∈ M := by
  have hc := conditions_mem M B hM hT hB
  have hR := restrictionGraph_mem M A B hM hT hA hB
  let e := cons (conditions B) (cons (restrictionGraph A B) (fun _ => D))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hc; exact hR; exact hD
  simpa only [densePreimage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 3) (.member 0 4))) e he
      (conditions_mem M A hM hT hA)

theorem label_densePreimage (A B D : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) :
    label _ p ∈ densePreimage A B D ↔ label _ (project A B hBA p) ∈ D := by
  rw [densePreimage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,_,hq,hqD⟩
    have he := ((pair_restrictionGraph A B _ q).mp hq).2.2
    rw [label_project,←he]; exact hqD
  · intro h
    exact ⟨label_mem _ p,label _ (project A B hBA p),label_mem _ _,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,h⟩

theorem densePreimage_dense (A B D : ZFSet.{0}) (hBA : B ⊆ A)
    (hD : Dense {q : Conditions (conditions B) | label _ q ∈ D}) :
    Dense {p : Conditions (conditions A) | label _ p ∈ densePreimage A B D} := by
  intro p
  let e := factorIso A B hBA
  obtain ⟨q,hq,hqD⟩ := hD (e p).1
  let r := e.symm (q,(e p).2)
  have hr : e r = (q,(e p).2) := e.apply_symm_apply _
  refine ⟨r,?_,?_⟩
  · apply e.le_iff_le.mp
    rw [hr]
    exact ⟨hq,le_rfl⟩
  · apply (label_densePreimage A B D hBA r).mpr
    have he := congrArg Prod.fst hr
    change project A B hBA r = q at he
    rw [he]; exact hqD

theorem projected_groundGeneric (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (projected A B hBA G) := by
  intro D hD hd
  obtain ⟨p,hp,hpD⟩ := hG (densePreimage A B D) (densePreimage_mem M A B D hM hT hA hB hD)
    (densePreimage_dense A B D hBA hd)
  exact ⟨project A B hBA p,(mem_projected A B hBA G _).mpr ⟨p,hp,rfl⟩,
    (label_densePreimage A B D hBA p).mp hpD⟩

theorem projected_contains (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) {p : Conditions (conditions A)}
    (hp : p ∈ G.carrier) : project A B hBA p ∈ (projected A B hBA G).carrier :=
  (mem_projected A B hBA G _).mpr ⟨p,hp,rfl⟩

end TuringRigidity.InternalCohenProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenProjectionSymmetry
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenProjectionSymmetry
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem project_fixed (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (a : Conditions (conditions A) ≃o Conditions (conditions A))
    (hfix : ∀ s, restrict B (label _ (a s)) = restrict B (label _ s))
    (s : Conditions (conditions A)) : project A B hBA (a s) = project A B hBA s := by
  apply label_injective
  simpa only [label_project] using hfix s

theorem projected_carrier_fixed (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (a : Conditions (conditions A) ≃o Conditions (conditions A))
    (hfix : ∀ s, restrict B (label _ (a s)) = restrict B (label _ s))
    (G : GenericFilter (Conditions (conditions A))) :
    (projected A B hBA (mapFilter a G)).carrier = (projected A B hBA G).carrier := by
  apply Set.ext; intro q
  rw [mem_projected,mem_projected]
  constructor
  · rintro ⟨p,hp,hpq⟩
    refine ⟨a.symm p,hp,?_⟩
    have hh := project_fixed A B hBA a hfix (a.symm p)
    rw [a.apply_symm_apply] at hh
    exact hh.symm.trans hpq
  · rintro ⟨p,hp,hpq⟩
    exact ⟨a p,by simpa only [mapFilter,Set.mem_ofPred_eq,a.symm_apply_apply] using hp,
      (project_fixed A B hBA a hfix p).trans hpq⟩

end TuringRigidity.InternalCohenProjectionSymmetry

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFunctionOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem mem_orbitGraph (a : ℕ → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ orbitGraph a ↔ ∃ n, z = ZFSet.pair (natSet n) (a n) := by
  rw [orbitGraph,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

theorem orbitGraph_pair (a : ℕ → ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ orbitGraph a ↔ x = a n := by
  rw [mem_orbitGraph]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    have hnm := natSet_injective hn
    exact hnm.symm ▸ hx
  · intro h; exact ⟨n,congrArg (ZFSet.pair (natSet n)) h⟩

theorem orbitGraph_function (d : ZFSet.{u}) (a : ℕ → ZFSet.{u}) (ha : ∀ n, a n ∈ d) :
    TransitiveNameModel.FunctionGraph ZFSet.omega d (orbitGraph a) := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph a z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨a n,ha n,(orbitGraph_pair a n _).mpr rfl,fun y _ hy => (orbitGraph_pair a n y).mp hy⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNaturalCheckSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalNaturalCheckSequence
open TransitiveNameModel BoundedSetTheory

theorem natural_check_sequence (M t : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ht : t ∈ M) : orbitGraph (fun n => checkedCode t (natSet n)) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union hS
    hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨g,hgM,hg⟩ := internal_checkGraph M d q t hM hT.pairing hT.union hT.powerSet hS
    hT.replacement.finitePrefix hdM hqM ht hd hq ZFSet.omega hωd
  let r := iterUnion 2 g
  have hrM : r ∈ M := iterUnion_mem M hM hT.union hgM 2
  have hn (n : ℕ) : natSet n ∈ hull d q ZFSet.omega :=
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  have hpair (n : ℕ) (v : ZFSet.{0}) :
      ZFSet.pair (natSet n) v ∈ g ↔ v = checkedCode t (natSet n) := by
    rw [hg.mem_iff]
    constructor
    · rintro ⟨w,_,hp⟩
      obtain ⟨he,hv⟩ := ZFSet.pair_inj.mp hp
      exact he.symm ▸ hv
    · intro hv
      exact ⟨natSet n,hn n,congrArg (ZFSet.pair (natSet n)) hv⟩
  have hv (n : ℕ) : checkedCode t (natSet n) ∈ r :=
    second_mem_doubleUnion ((hpair n _).mpr rfl)
  let e := cons ZFSet.omega (cons r (fun _ => g))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (.pairMem 1 0 5)))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hω; exact hrM; exact hgM
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      z ∈ orbitGraph (fun n => checkedCode t (natSet n)) := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,v,_,hz,hnv⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      exact (mem_orbitGraph _ z).mpr ⟨n,by rw [hz,(hpair n v).mp hnv]⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph _ z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,_,hv n,rfl,(hpair n _).mpr rfl⟩
  have hh := sep_mem M hM hS φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hrM)
  have heq : (ZFSet.prod ZFSet.omega r).sep (fun z => φ.Eval (cons z e)) =
      orbitGraph (fun n => checkedCode t (natSet n)) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function r _ hv).1 z hz),hz⟩⟩
  exact heq ▸ hh

end TuringRigidity.InternalNaturalCheckSequence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNiceName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalNiceName
open TransitiveNameModel BoundedSetTheory RecursiveNames CountableForcing
variable {c : ZFSet.{0}} [Top (Conditions c)]

theorem mem_encode_nice (E : ℕ → ZFSet.{0}) (z : ZFSet.{0}) :
    z ∈ (nice E : Name (Conditions c)).encode (label c) ↔
      ∃ n, ∃ p : Conditions c, label c p ∈ E n ∧
        z = ZFSet.pair (checkedCode (label c ⊤) (natSet n)) (label c p) := by
  simp only [nice,Name.encode,ZFSet.mem_range,encode_check]
  exact ⟨fun ⟨⟨n,p,hp⟩,hz⟩ => ⟨n,p,hp,hz.symm⟩,
    fun ⟨n,p,hp,hz⟩ => ⟨⟨n,p,hp⟩,hz.symm⟩⟩

theorem nice_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hEgraph : orbitGraph E ∈ M) :
    (nice E : Name (Conditions c)).encode (label c) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hEQ : ∀ n, E n ∈ Q := fun n => (hQ _).mpr (hE n)
  let B := orbitGraph (fun n => checkedCode (label c ⊤) (natSet n))
  have hBM : B ∈ M := InternalNaturalCheckSequence.natural_check_sequence M _ hM hT
    (hM c hc _ (label_mem c ⊤))
  let r := iterUnion 2 B
  have hrM := iterUnion_mem M hM hT.union hBM 2
  have hr (n : ℕ) : checkedCode (label c ⊤) (natSet n) ∈ r :=
    second_mem_doubleUnion ((orbitGraph_pair _ n _).mpr rfl)
  let e := cons ZFSet.omega (cons Q (cons r (cons c (cons B (fun _ => orbitGraph E)))))
  let φ : BoundedSetTheory.Formula := .existsMem 1 (.existsMem 3 (.existsMem 5 (.existsMem 7
    (.conj (.orderedPair 4 1 0) (.conj (.pairMem 3 1 9)
      (.conj (.pairMem 3 2 10) (.member 0 2)))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hω; exact hQM; exact hrM; exact hc; exact hBM; exact hEgraph
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      z ∈ (nice E : Name (Conditions c)).encode (label c) := by
    simp only [φ,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_orderedPair,BoundedSetTheory.Formula.eval_pairMem,cons_zero,cons_succ,e]
    rw [mem_encode_nice]
    constructor
    · rintro ⟨n,hn,H,_,v,_,p,hp,hz,hnv,hnH,hpH⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨p,rfl⟩ := label_surjective c hp
      have hv := (orbitGraph_pair _ n v).mp hnv
      have hH := (orbitGraph_pair E n H).mp hnH
      exact ⟨n,p,hH ▸ hpH,by rw [hz,hv]⟩
    · rintro ⟨n,p,hp,rfl⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hEQ n,_,hr n,_,label_mem c p,rfl,
        (orbitGraph_pair _ n _).mpr rfl,(orbitGraph_pair E n _).mpr rfl,hp⟩
  have hs := sep_mem M hM hS φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hrM hc)
  have heq : (ZFSet.prod r c).sep (fun z => φ.Eval (cons z e)) =
      (nice E : Name (Conditions c)).encode (label c) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    refine ⟨And.right,fun hz => ⟨?_,hz⟩⟩
    obtain ⟨n,p,_,rfl⟩ := (mem_encode_nice E z).mp hz
    exact ZFSet.mem_prod.mpr ⟨_,hr n,_,label_mem c p,rfl⟩
  exact heq ▸ hs

theorem mem_val_nice (E : ℕ → ZFSet.{0}) (G : Set (Conditions c)) (hG : ⊤ ∈ G)
    (x : ZFSet.{0}) : x ∈ (nice E : Name (Conditions c)).val G ↔
      ∃ n, ∃ p ∈ G, label c p ∈ E n ∧ natSet n = x := by
  rw [nice,Name.mem_val]
  simp only [Name.val_check _ hG]
  exact ⟨fun ⟨⟨n,p,hp⟩,hpG,hx⟩ => ⟨n,p,hpG,hp,hx⟩,
    fun ⟨n,p,hpG,hp,hx⟩ => ⟨⟨n,p,hp⟩,hpG,hx⟩⟩

end TuringRigidity.InternalNiceName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenSupportedValue
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenSupportedValue
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset CohenInternalSupport InternalCohenRestriction InternalCohenPartition
open InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem supported_hit_iff (A B E : ZFSet.{0}) (hBA : B ⊆ A) (hE : E ⊆ conditions B)
    (G : GenericFilter (Conditions (conditions A))) :
    (∃ p ∈ G.carrier, label _ p ∈ E) ↔
      ∃ q ∈ (projected A B hBA G).carrier, label _ q ∈ E := by
  constructor
  · rintro ⟨p,hp,hpE⟩
    refine ⟨project A B hBA p,projected_contains A B hBA G hp,?_⟩
    rw [label_project,restrict_eq_self B _ (hE hpE)]; exact hpE
  · rintro ⟨q,hq,hqE⟩
    obtain ⟨p,hp,hpq⟩ := (mem_projected A B hBA G q).mp hq
    have hqA := condition_mono A B (label _ q) hBA (label_mem _ q)
    obtain ⟨r,hr⟩ := label_surjective (conditions A) hqA
    refine ⟨r,G.upper (p := p) ?_ hp,?_⟩
    · change label _ r ⊆ label _ p
      rw [hr,←hpq,label_project]
      exact fun _ h => (ZFSet.mem_sep.mp h).1
    · rwa [hr]

theorem nice_value_projected (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ⊆ conditions B)
    (G : GenericFilter (Conditions (conditions A))) :
    (InternalNiceName.nice E : Name (Conditions (conditions B))).val (projected A B hBA G).carrier =
      (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier := by
  obtain ⟨p,hp⟩ := G.nonempty
  have htA : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  let H := projected A B hBA G
  obtain ⟨q,hq⟩ := H.nonempty
  have htB : (⊤ : Conditions (conditions B)) ∈ H.carrier := H.upper le_top hq
  apply ZFSet.ext; intro x
  rw [InternalNiceName.mem_val_nice E _ htB,InternalNiceName.mem_val_nice E _ htA]
  constructor
  · rintro ⟨n,q,hq,hqE,hx⟩
    obtain ⟨p,hp,hpE⟩ := (supported_hit_iff A B (E n) hBA (hE n) G).mpr ⟨q,hq,hqE⟩
    exact ⟨n,p,hp,hpE,hx⟩
  · rintro ⟨n,p,hp,hpE,hx⟩
    obtain ⟨q,hq,hqE⟩ := (supported_hit_iff A B (E n) hBA (hE n) G).mp ⟨p,hp,hpE⟩
    exact ⟨n,q,hq,hqE,hx⟩

end TuringRigidity.InternalCohenSupportedValue

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenProjectedNameLift
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenProjectedNameLift
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenSupportedValue
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem lift_projected_real_name_oai (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M) :
    ∃ y : Name (Conditions (conditions A)), y.encode (label (conditions A)) ∈ M ∧
      (∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        τ.val (projected A B hBA G).carrier ⊆ ZFSet.omega →
          y.val G.carrier = τ.val (projected A B hBA G).carrier) ∧
      ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
        (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
        ∀ G : GenericFilter (Conditions (conditions A)),
          y.val (AutomorphismName.mapFilter a G).carrier = y.val G.carrier := by
  obtain ⟨E,hgraph,hE,_,_,hval⟩ :=
    CohenNiceNameConstruction.internal_nice_name M B hM hT hB τ hτ
  have hEB (n : ℕ) : E n ⊆ conditions B :=
    fun p hp => (ZFSet.mem_sep.mp ((hE n).2.1 hp)).1
  have hEA (n : ℕ) : E n ⊆ conditions A :=
    fun p hp => condition_mono A B p hBA (hEB n hp)
  let y : Name (Conditions (conditions A)) := InternalNiceName.nice E
  refine ⟨y,InternalNiceName.nice_internal M hM hT (conditions_mem M A hM hT hA) E
    (fun n => ⟨(hE n).1,hEA n⟩) hgraph,?_,?_⟩
  · intro G hG hreal
    exact (nice_value_projected A B hBA E hEB G).symm.trans
      (hval _ (projected_groundGeneric M A B hM hT hA hB hBA G hG) hreal)
  · intro a hfix G
    change (InternalNiceName.nice E : Name (Conditions (conditions A))).val _ = _
    rw [←nice_value_projected A B hBA E hEB (AutomorphismName.mapFilter a G),
      projected_carrier_fixed A B hBA a hfix G,nice_value_projected A B hBA E hEB G]

end TuringRigidity.CohenProjectedNameLift

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name_oai := @OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name_oai
