-- Prove2me | solution 1 for OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:57:12.289644+00:00
-- url     : https://prove2.me/submissions/28b0aa6e-9f18-4a82-adc2-9a565d11a1de

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_InternalCohen_prefix_extension_eq_hull

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

namespace SentenceForm

theorem sat_rename (p : SentenceForm) (v : ℕ → ℕ)
    (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Sat D e ↔ p.Sat D (fun i => e (v i)) := by
  induction p generalizing v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp v e) (ihq v e)
  | neg p ih => exact not_congr (ih v e)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih _ _).trans (he ▸ Iff.rfl)
end SentenceForm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalAtomicTruth
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_atomic_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    (Name.val G.carrier a = Name.val G.carrier b ↔ ∃ p ∈ G.carrier, EqForces a b p) ∧
    (Name.val G.carrier a ∈ Name.val G.carrier b ↔ ∃ p ∈ G.carrier, MemForces a b p) := by
  have hg := groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG
  exact ⟨eq_truth (names_childClosed M c hM) G hg a b ha hb,
    mem_truth (names_childClosed M c hM) G hg a b ha hb⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericFilterName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

theorem val_genericFilterName (p : ZFSet.{u}) [Top (Conditions p)]
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (genericFilterName p).val G = genericFilterSet p G := by
  apply ZFSet.ext; intro x
  simp only [genericFilterName,Name.mem_val,Name.val_check G hG,mem_genericFilterSet,id_eq]

theorem eval_filterCodeFormula (z p f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    filterCodeFormula.Eval (cons z (cons p (cons f (cons r e)))) ↔
      ∃ x ∈ p, ∃ v ∈ r, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  simp only [filterCodeFormula,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_filterCode (p f z : ZFSet.{u}) :
    z ∈ filterCode p f ↔ ∃ x ∈ p, ∃ v, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  rw [filterCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,v,_,hv,hz⟩; exact ⟨x,hx,v,hv,hz⟩
  · rintro ⟨x,hx,v,hv,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,x,hx,rfl⟩,x,hx,v,hr,hv,rfl⟩

theorem filterCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {p f : ZFSet.{u}} (hp : p ∈ M) (hf : f ∈ M) : filterCode p f ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons p (cons f (cons (iterUnion 2 f) (fun _ => p)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hp
    rcases i with _|i; exact hf
    rcases i with _|i; exact hr
    exact hp
  have hs := sep_mem M hM hS filterCodeFormula e he
    (product_mem M hM hP hU hPow hS hr hp)
  have heq : ZFSet.sep (fun z => filterCodeFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) p) = filterCode p f := by
    apply ZFSet.ext; intro z
    simp only [filterCode,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_filterCodeFormula z p f _ _)
  exact heq ▸ hs

theorem encode_genericFilterName (p d r f : ZFSet.{u}) [Top (Conditions p)]
    (hsub : p ⊆ d) (hf : CheckGraph d r f (label p ⊤)) :
    (genericFilterName p).encode (label p) = filterCode p f := by
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_filterCode]
  constructor
  · rintro ⟨q,hq⟩
    have hx := hsub (label_mem p q)
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 (label p q) hx
    have he := hf.correct _ hx v hv hfv
    refine ⟨label p q,label_mem p q,v,hfv,?_⟩
    simpa only [genericFilterName,id_eq,encode_check,he] using hq.symm
  · rintro ⟨x,hx,v,hfv,hz⟩
    obtain ⟨q,rfl⟩ := label_surjective p hx
    have hfr : FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
    have he := hf.correct _ (hsub hx) v (hfr.value_mem hfv) hfv
    exact ⟨q,by simpa only [genericFilterName,id_eq,encode_check,he] using hz.symm⟩

theorem genericFilterName_mem (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) : genericFilterName p ∈ names M p := by
  obtain ⟨d,hdM,hd,hpd⟩ := internal_transitive_container M hM hP hU hS hR hI hp
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label p ⊤) hM hP hU hPow hS hR
    hdM hqM (hM p hp _ (label_mem p ⊤)) hd hq p hpd
  have hsub : p ⊆ hull d q p := fun x hx =>
    hull_transitive d q p hd p (self_mem_hull d q hpd) x hx
  change (genericFilterName p).encode (label p) ∈ M
  rw [encode_genericFilterName p _ _ f hsub hfg]
  exact filterCode_mem M hM hP hU hPow hS hp hf

theorem genericFilterSet_mem_extension (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    genericFilterSet p G ∈ genericExtensionSet M p G :=
  (mem_extensionSet M p G _).mpr ⟨genericFilterName p,
    genericFilterName_mem M p hM hP hU hPow hS hR hI hp,val_genericFilterName p G hG⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem bounded_sat (p : Formula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => and_congr_right (fun _ => ih (cons x e)))

theorem sigma_sat (p : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromSigma p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | bounded p => exact bounded_sat p M e
  | existsSet p ih =>
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_FullSetForcing
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm BoundedForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem realize_code (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SentenceForm) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (code φ ci oi pi v).Sat (M : Set ZFSet) env ↔ Forces M e φ p := by
  have hS := hT.separation.finitePrefix.bounded
  have hR := hT.replacement.finitePrefix
  induction φ generalizing e p env ci oi pi v with
  | equal i j =>
    exact (sigma_sat _ M env).trans (realize_sigmaForcing M hM hT.pairing hT.union hT.powerSet hS hR
      hT.infinity ho (.bounded (.equal i j)) e p env henv ci oi pi v hc ho' hp hv)
  | member i j =>
    exact (sigma_sat _ M env).trans (realize_sigmaForcing M hM hT.pairing hT.union hT.powerSet hS hR
      hT.infinity ho (.bounded (.member i j)) e p env henv ci oi pi v hc ho' hp hv)
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e p env henv ci oi pi v hc ho' hp hv)
      (ihψ e p env henv ci oi pi v hc ho' hp hv)
  | neg φ ih =>
    have hcM : c ∈ M := hc ▸ henv ci
    have pair (q : Conditions c) :
        (fromBounded (Formula.pairMem 0 (pi+1) (oi+1))).Sat
          (M : Set ZFSet) (cons (label c q) env) ↔ q ≤ p := by
      rw [bounded_sat,Formula.absolute _ M hM _ (by intro i; cases i; exact hM c hcM _ (label_mem c q); exact henv _)]
      simp only [Formula.eval_pairMem,cons_zero,cons_succ,hp,ho']
      exact ho q p
    have sub (q : Conditions c) := ih e q (cons (label c q) env)
      (by intro i; cases i; exact hM c hcM _ (label_mem c q); exact henv _)
      (ci+1) (oi+1) 0 (fun i => v i+1) hc ho' rfl hv
    simp only [code,sat_all,sat_imp,Sat,cons_zero,cons_succ,hc]
    constructor
    · intro h q hq hf
      exact h _ (hM c hcM _ (label_mem c q)) (label_mem c q) ((pair q).mpr hq) ((sub q).mpr hf)
    · intro h x _ hx hxp hf
      obtain ⟨q,rfl⟩ := label_surjective c hx
      exact h q ((pair q).mp hxp) ((sub q).mp hf)
  | ex φ ih =>
    have henv' (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x env i ∈ M := by
      intro i; cases i; exact hx; exact henv _
    have valid (x : ZFSet.{u}) (hx : x ∈ M) :
        (fromSigma (NameValidity.Code.valid (ci+1) 0)).Sat (M : Set ZFSet) (cons x env) ↔
          ∃ a : Name (Conditions c), a.encode (label c) = x := by
      rw [sigma_sat]
      have h := NameValidity.realize_valid M hM hT.pairing hT.union hT.powerSet hS hR hT.infinity
        (cons x env) (henv' x hx) (ci+1) 0
      change (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
        (∃ a : Name (Conditions (env ci)), a.encode (label (env ci)) = x) at h
      rw [hc] at h
      exact h
    have sub (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :=
      ih (push a e) p (cons (a.encode (label c)) env) (henv' _ ha)
        (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1)) hc ho' hp
        (by intro i; cases i <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    simp only [code,Sat]
    constructor
    · rintro ⟨x,hx,hvalid,hforce⟩
      obtain ⟨a,rfl⟩ := (valid x hx).mp hvalid
      exact ⟨a,hx,(sub a hx).mp hforce⟩
    · rintro ⟨a,ha,hforce⟩
      exact ⟨_,ha,(valid _ ha).mpr ⟨a,rfl⟩,(sub a ha).mpr hforce⟩

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseCounting
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem mem_unionGraph {c : ZFSet.{u}} (G : GenericFilter (Conditions c)) (z : ZFSet.{u}) :
    z ∈ unionGraph G ↔ ∃ p ∈ G.carrier, z ∈ label c p := by
  rw [unionGraph,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p,hp,hz⟩
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,hq,hz⟩
  · rintro ⟨p,hp,hz⟩
    exact ⟨label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hz⟩

theorem unionGraph_mem_extension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (hcM : c ∈ M) (h0 : (∅ : ZFSet.{u}) ∈ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M c G.carrier := by
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have hE := extension_sourceT M hM hT hcM (orderSet_mem M hM hT hcM) (orderSet_pair c) G hG htop
  apply union_mem _ (genericExtensionSet_transitive M c hM G.carrier) hE.union
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcM G.carrier htop

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryCheckedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm
universe u

theorem checkedValue_sound (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (h : checkedValueFormula.Sat (M : Set ZFSet) e) : e 0 = checkedCode (e 2) (e 1) := by
  obtain ⟨d,hd,r,hr,f,hf,h⟩ := h
  have hi : ∀ i, cons f (cons r (cons d e)) i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hf
    exact hr
    exact hd
    exact he i
  rw [bounded_sat,Formula.absolute _ M hM _ hi] at h
  simp only [Formula.Eval,CheckFormula.eval_graph,Formula.eval_pairMem,cons_zero,cons_succ] at h
  exact h.1.correct (e 1) h.2.1 (e 0) h.2.2.1 h.2.2.2

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCheckedValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

theorem checkedValue_complete (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hv : e 0 = checkedCode (e 2) (e 1)) :
    checkedValueFormula.Sat (M : Set ZFSet) e := by
  have hS := hT.separation.finitePrefix.bounded
  have hR := hT.replacement.finitePrefix
  obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hT.pairing hT.union hS hR
    hT.infinity (he 1)
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hT.powerSet hd
  obtain ⟨f,hf,hg⟩ := internal_checkGraph M d q (e 2) hM hT.pairing hT.union hT.powerSet
    hS hR hd hq (he 2) hdT hqdef (e 1) hxd
  have hh := hull_mem M d q hM hS hd hq (he 1)
  have hr := iterUnion_mem M hM hT.union hf 2
  have hx := self_mem_hull d q hxd
  obtain ⟨w,hw,hfw,_⟩ := hg.2.2.1 (e 1) hx
  have hwv : w = e 0 := (hg.correct (e 1) hx w hw hfw).trans hv.symm
  refine ⟨BoundedSetTheory.hull d q (e 1),hh,iterUnion 2 f,hr,f,hf,?_⟩
  have hi : ∀ i, cons f (cons (iterUnion 2 f) (cons (BoundedSetTheory.hull d q (e 1)) e)) i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hf
    exact hr
    exact hh
    exact he i
  rw [bounded_sat,Formula.absolute _ M hM _ hi]
  simp only [Formula.Eval,CheckFormula.eval_graph,Formula.eval_pairMem,cons_zero,cons_succ]
  exact ⟨hg,hx,hwv ▸ hw,hwv ▸ hfw⟩

theorem checkedValue_spec (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    checkedValueFormula.Sat (M : Set ZFSet) e ↔ e 0 = checkedCode (e 2) (e 1) :=
  ⟨checkedValue_sound M hM e he,checkedValue_complete M hM hT e he⟩

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedMembershipSeparation
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem checkedMembership_spec (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {o : ZFSet.{u}} (ho : ∀ r s : Conditions c,
      ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (p : Conditions c) (x : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (h0 : e 0 = x) (h1 : e 1 = c) (h2 : e 2 = o) (h3 : e 3 = label c p)
    (h4 : e 4 = t.encode (label c)) (h5 : e 5 = label c ⊤) :
    checkedMembershipFormula.Sat (M : Set ZFSet) e ↔ MemForces (Name.check x) t p := by
  let v : ℕ → ℕ := fun i => match i with | 0 => 0 | _ => 5
  let k : ℕ → ℕ := fun i => match i with | 0 => 0 | 1 => 1 | _ => 6
  let names : ℕ → Name (Conditions c) := fun i => match i with | 0 => Name.check x | _ => t
  have hc : c ∈ M := h1 ▸ he 1
  have hx : x ∈ M := h0 ▸ he 0
  have hcheck : (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  have henv (z : ZFSet.{u}) (hz : z ∈ M) : ∀ i, cons z e i ∈ M := by
    intro i; cases i; exact hz; exact he _
  have checked (z : ZFSet.{u}) (hz : z ∈ M) :
      (checkedValueFormula.rename k).Sat (M : Set ZFSet) (cons z e) ↔
        z = (Name.check x : Name (Conditions c)).encode (label c) := by
    rw [sat_rename,checkedValue_spec M hM hT _ (fun i => henv z hz (k i))]
    simp only [k,cons_zero,cons_succ,h0,h5,encode_check]
  have forcing (z : ZFSet.{u}) (hz : z ∈ M)
      (hzv : z = (Name.check x : Name (Conditions c)).encode (label c)) :
      (code (.member 0 1) 2 3 4 v).Sat (M : Set ZFSet) (cons z e) ↔
        MemForces (Name.check x) t p := by
    exact realize_code M hM hT ho (.member 0 1) names p (cons z e) (henv z hz)
      2 3 4 v h1 h2 h3 (by intro i; cases i; exact hzv; exact h4)
  change (∃ z ∈ M, (checkedValueFormula.rename k).Sat _ (cons z e) ∧ _) ↔ _
  constructor
  · rintro ⟨z,hz,hzv,hf⟩
    exact (forcing z hz ((checked z hz).mp hzv)).mp hf
  · intro hf
    exact ⟨_,hcheck,(checked _ hcheck).mpr rfl,(forcing _ hcheck rfl).mpr hf⟩

theorem checkedMembershipSigma_spec (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    checkedMembershipSigma.Realize M e ↔ checkedMembershipFormula.Sat (M : Set ZFSet) e := by
  change (∃ z ∈ M, (SigmaFormula.conj _ _).Realize M (cons z e)) ↔
    ∃ z ∈ M, (SentenceForm.conj _ _).Sat (M : Set ZFSet) (cons z e)
  apply exists_congr; intro z
  apply and_congr_right; intro _
  rw [SigmaFormula.realize_conj]
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [SigmaFormula.realize_rename,sat_rename]
  exact and_congr (sigma_sat checkedValueSigma M _).symm
    (sigma_sat (BoundedForcing.SigmaCode.forcing (.bounded (.member 0 1)) 2 3 4
      (fun i => match i with | 0 => 0 | _ => 5)) M _).symm

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CheckedForcingRelation
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CheckedForcingRelation
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
variable {c : ZFSet.{0}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem pair_relation (a x : ZFSet.{0}) (τ : Name (Conditions c)) (p : Conditions c) :
    ZFSet.pair x (label c p) ∈ relation a τ ↔ x ∈ a ∧ MemForces (Name.check x) τ p := by
  rw [relation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,q,he,hf⟩
    have hpq := label_injective c (ZFSet.pair_inj.mp he).2
    have hxy := (ZFSet.pair_inj.mp he).1
    subst y; subst q; exact ⟨hy,hf⟩
  · rintro ⟨hx,hf⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,_,label_mem c p,rfl⟩,x,hx,p,rfl,hf⟩

theorem relation_mem (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (ha : a ∈ M) {o : ZFSet.{0}} (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (τ : Name (Conditions c)) (hτ : τ.encode (label c) ∈ M) : relation a τ ∈ M := by
  let e := cons a (cons c (cons o (cons (τ.encode (label c)) (fun _ => label c ⊤))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact ha; exact hc; exact hoM; exact hτ; exact hM c hc _ (label_mem c ⊤)
  let ren : ℕ → ℕ := fun | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 6 | _ => 7
  let φ : SigmaFormula := .existsMem 1 (.existsMem 3 (.andBounded (.orderedPair 2 1 0)
    (FullSetForcing.checkedMembershipSigma.rename ren)))
  have hpM := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hc
  obtain ⟨R,hRM,hR⟩ := hT.separation.finitePrefix φ e he (ZFSet.prod a c) hpM
  have spec (x y z : ZFSet.{0}) (hx : x ∈ M) (hy : y ∈ M)
      (p : Conditions c) (hpy : label c p = y) :
      (FullSetForcing.checkedMembershipSigma.rename ren).Realize M (cons y (cons x (cons z e))) ↔
        MemForces (Name.check x) τ p := by
    rw [SigmaFormula.realize_rename,FullSetForcing.checkedMembershipSigma_spec]
    have hv : ∀ i, (cons y (cons x (cons z e)) ∘ ren) i ∈ M := by
      intro i; rcases i with _|_|_|_|_|i
      exact hx; exact hc; exact hoM; exact hy; exact hτ; exact he 4
    exact FullSetForcing.checkedMembership_spec M hM hT ho τ p x _ hv
      rfl rfl rfl hpy.symm rfl rfl
  have pairSpec (x y z : ZFSet.{0}) (hx : x ∈ M) (hy : y ∈ M) (hz : z ∈ M) :
      (BoundedSetTheory.Formula.orderedPair 2 1 0).Realize M (cons y (cons x (cons z e))) ↔
        z = ZFSet.pair x y := by
    have hv : ∀ i, cons y (cons x (cons z e)) i ∈ M := by
      intro i; rcases i with _|_|_|i; exact hy; exact hx; exact hz; exact he i
    exact (BoundedSetTheory.Formula.absolute _ M hM _ hv).trans
      (by simp only [BoundedSetTheory.Formula.eval_orderedPair,cons_zero,cons_succ])
  have heq : R = relation a τ := by
    apply ZFSet.ext; intro z
    constructor
    · intro hzR
      have hz := hM R hRM z hzR
      obtain ⟨hzprod,hf⟩ := (hR z hz).mp hzR
      simp only [φ,SigmaFormula.realize_existsMem,SigmaFormula.realize_andBounded,
        cons_zero,cons_succ,e] at hf
      obtain ⟨x,hx,hxa,y,hy,hyc,hzxy,hf⟩ := hf
      obtain ⟨p,hpy⟩ := label_surjective c hyc
      exact ZFSet.mem_sep.mpr ⟨hzprod,x,hxa,p,((pairSpec x y z hx hy hz).mp hzxy).trans (congrArg (ZFSet.pair x) hpy.symm),
        (spec x y z hx hy p hpy).mp hf⟩
    · intro hzR
      obtain ⟨hzprod,x,hxa,p,hzxy,hf⟩ := ZFSet.mem_sep.mp hzR
      have hz := hM _ hpM z hzprod
      have hx := hM a ha x hxa
      have hy := hM c hc _ (label_mem c p)
      apply (hR z hz).mpr
      refine ⟨hzprod,?_⟩
      simp only [φ,SigmaFormula.realize_existsMem,SigmaFormula.realize_andBounded,
        cons_zero,cons_succ,e]
      exact ⟨x,hx,hxa,label c p,hy,label_mem c p,(pairSpec x (label c p) z hx hy hz).mpr hzxy,
        (spec x (label c p) z hx hy p rfl).mpr hf⟩
  exact heq ▸ hRM

end TuringRigidity.CheckedForcingRelation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenConditions
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

theorem conditions_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : conditions ∈ M := by
  obtain ⟨c,hc,hdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
    (alphabet_mem M hM hT)
  have he : c = conditions := ZFSet.ext (fun p => (hdef p).trans (mem_conditions p).symm)
  exact he ▸ hc

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGenericUnion
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGenericUnion
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenSymmetry CohenConditionCode CohenGroundPoset CohenGroundGeneric
open InternalCohen (alphabet mem_alphabet bitSet)
open InternalCollapse (unionGraph mem_unionGraph)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem definedAt_mem (M A x : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hx : x ∈ A) : definedAt A x ∈ M := by
  let e := cons alphabet (fun _ => x)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i
    exact InternalCohen.alphabet_mem M hM hT
    exact hM A hA x hx
  simpa only [definedAt,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.pairMem 3 0 1)) e he (conditions_mem M A hM hT hA)

theorem assign_dense {ι : Type*} (i : ι) :
    Dense {p : Condition ι | ∃ b, p.val i = some b} := by
  classical
  intro p
  cases hi : p.val i with
  | some b => exact ⟨p,le_rfl,b,hi⟩
  | none =>
    let q : Condition ι := {
      val j := if j = i then some false else p.val j
      finite := (p.finite.insert i).subset (by
        intro j hj
        by_cases he : j = i
        · exact Or.inl he
        · exact Or.inr (by simpa [he] using hj)) }
    refine ⟨q,?_,false,by simp [q]⟩
    intro j b hj
    by_cases he : j = i
    · subst j; rw [hi] at hj; cases hj
    · simpa [q,he] using hj

theorem definedAt_dense (A x : ZFSet.{0}) (hx : x ∈ A) :
    Dense {q : Conditions (conditions A) | label _ q ∈ definedAt A x} := by
  let i : Conditions A := equivShrink A ⟨x,hx⟩
  have hi : label A i = x := by simp [i,label]
  intro p
  obtain ⟨q,hq,b,hqb⟩ := assign_dense i ((conditionEquiv A).symm p)
  refine ⟨conditionEquiv A q,by simpa using (conditionEquiv A).monotone hq,?_⟩
  change label _ (encode A q) ∈ definedAt A x
  rw [label_encode,definedAt,ZFSet.mem_sep]
  refine ⟨(mem_conditions A _).mpr (graph_isCondition A q),bitSet b,
    (mem_alphabet _).mpr ⟨b,rfl⟩,?_⟩
  rw [←hi,pair_mem_graph]; exact hqb

theorem union_function (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Conditions (conditions A)))
    (hG : AtomicForcing.GroundGeneric M G) : FunctionGraph A alphabet (unionGraph G) := by
  constructor
  · intro z hz
    obtain ⟨p,_,hzp⟩ := (mem_unionGraph G z).mp hz
    have hp := ((mem_conditions A _).mp (label_mem _ p)).1
    exact ZFSet.mem_prod.mp (((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp hp).1 hzp)
  · intro x hx
    obtain ⟨p,hp,hpx⟩ := hG (definedAt A x) (definedAt_mem M A x hM hT hA hx)
      (definedAt_dense A x hx)
    obtain ⟨_,b,hb,hpb⟩ := ZFSet.mem_sep.mp hpx
    refine ⟨b,hb,(mem_unionGraph G _).mpr ⟨p,hp,hpb⟩,?_⟩
    intro c hc hxc
    obtain ⟨q,hq,hqc⟩ := (mem_unionGraph G _).mp hxc
    obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
    exact ((mem_conditions A _).mp (label_mem _ r)).2 x hx c hc b hb (hrq hqc) (hrp hpb)

theorem union_internal (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Conditions (conditions A)))
    (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M (conditions A) G.carrier ∧
      FunctionGraph A alphabet (unionGraph G) :=
  ⟨InternalCollapse.unionGraph_mem_extension M hM hT (conditions_mem M A hM hT hA)
      (empty_mem_conditions A) G hG,
    union_function M A hM hT hA G hG⟩

theorem manyColumn_union (M K : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hK : K ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
      FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G) :=
  union_internal M _ hM hT (product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)) G hG

end TuringRigidity.CohenGenericUnion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet)

theorem eval_realNameFormula (z c f r one C a : ZFSet.{0}) (e : ℕ → ZFSet.{0}) :
    realNameFormula.Eval
      (cons z (cons c (cons ZFSet.omega (cons f (cons r (cons one (cons C (cons a e)))))))) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ r, ∃ x ∈ C,
        ZFSet.pair n v ∈ f ∧ x = ZFSet.pair a n ∧
        ZFSet.pair x one ∈ q ∧ z = ZFSet.pair v q := by
  simp only [realNameFormula,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_pairMem,
    BoundedSetTheory.Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_realNameCode (K a f z : ZFSet.{0}) (ha : a ∈ K) : z ∈ realNameCode K a f ↔
    ∃ q ∈ poset K, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair (ZFSet.pair a n) (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  rw [realNameCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,n,hn,v,_,x,_,hv,rfl,hbit,hz⟩; exact ⟨q,hq,n,hn,v,hv,hbit,hz⟩
  · rintro ⟨q,hq,n,hn,v,hv,hbit,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,q,hq,rfl⟩,q,hq,n,hn,v,hr,ZFSet.pair a n,ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩,hv,rfl,hbit,rfl⟩

theorem realNameCode_mem (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode K a f ∈ M := by
  have hc := (CohenGroundPoset.manyColumn_internal M K hM hT hK).1
  have hω := sourceT_omega_mem M hM hT
  have hr := iterUnion_mem M hM hT.union hf 2
  have h1 : bitSet true ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hK hω
  have haM := hM K hK a ha
  let e := cons (poset K) (cons ZFSet.omega (cons f (cons (iterUnion 2 f) (cons (bitSet true) (cons (ZFSet.prod K ZFSet.omega) (cons a (fun _ => a)))))))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|_|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded realNameFormula e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hr hc)
  have heq : ZFSet.sep (fun z => realNameFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) (poset K)) = realNameCode K a f := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,realNameCode]
    exact and_congr_right (fun _ => eval_realNameFormula z (poset K) f (iterUnion 2 f) (bitSet true)
      (ZFSet.prod K ZFSet.omega) a (fun _ => a))
  exact heq ▸ hs

theorem encode_realName (K a d r f : ZFSet.{0}) (ha : a ∈ K) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label (poset K) ⊤)) :
    (realName K a).encode (label (poset K)) = realNameCode K a f := by
  have hfr : TransitiveNameModel.FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_realNameCode K a f z ha]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hz⟩
    have hn := (mem_omega (natSet n)).mpr ⟨n,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 _ (hω hn)
    have he := hf.correct _ (hω hn) v hv hfv
    refine ⟨label (poset K) q,label_mem _ _,natSet n,hn,v,hfv,hbit,?_⟩
    simpa only [realName,encode_check,he] using hz.symm
  · rintro ⟨q,hq,n,hn,v,hfv,hbit,hz⟩
    obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨q,rfl⟩ := label_surjective (poset K) hq
    have he := hf.correct _ (hω hn) v (hfr.value_mem hfv) hfv
    exact ⟨⟨(q,k),hbit⟩,by simpa only [realName,encode_check,he] using hz.symm⟩

theorem realName_internal (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K) :
    (realName K a).encode (label (poset K)) ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label (poset K) ⊤) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM hqM (hM _ ((CohenGroundPoset.manyColumn_internal M K hM hT hK).1) _ (label_mem (poset K) ⊤)) hd hq ZFSet.omega hωd
  have hsub : ZFSet.omega ⊆ hull d q ZFSet.omega := fun x hx =>
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) x hx
  rw [encode_realName K a _ _ f ha hsub hfg]
  exact realNameCode_mem M K a hM hT hK ha hf

end TuringRigidity.CohenColumnRealName

end OAI
end

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenPartition
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohenRestriction
open InternalCohen (alphabet)

theorem complement_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : A \ B ∈ M := by
  simpa only [ZFSet.sep_notMem,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => B) (fun _ => hB) hA

end TuringRigidity.InternalCohenPartition

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenFilter
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenFilter
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCollapse
open InternalCohen (alphabet bitSet mem_alphabet bitSet_injective)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem finite_covered {c : ZFSet.{0}} (G : GenericFilter (Conditions c))
    (S : Set ZFSet.{0}) (hS : S.Finite)
    (hsub : ∀ z ∈ S, z ∈ unionGraph G) :
    ∃ p ∈ G.carrier, ∀ z ∈ S, z ∈ label c p := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨p,hp,fun _ h => False.elim h⟩
  | @insert z S hz hS ih =>
    obtain ⟨p,hp,hpS⟩ := ih (fun x hx => hsub x (Or.inr hx))
    obtain ⟨q,hq,hqz⟩ := (mem_unionGraph G z).mp (hsub z (Or.inl rfl))
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    refine ⟨r,hr,fun x hx => ?_⟩
    rcases hx with rfl|hx
    · exact hrq hqz
    · exact hrp (hpS x hx)

theorem mem_filter_iff_subset_union (A : ZFSet.{0})
    (G : GenericFilter (Conditions (conditions A)))
    (p : Conditions (conditions A)) :
    p ∈ G.carrier ↔ label _ p ⊆ unionGraph G := by
  constructor
  · intro hp z hz
    exact (mem_unionGraph G z).mpr ⟨p,hp,hz⟩
  · intro hsub
    have hfin := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions A _).mp (label_mem _ p)).1).2
    obtain ⟨q,hq,hqp⟩ := finite_covered G (label _ p) hfin (fun z hz => hsub hz)
    exact G.upper hqp hq

end TuringRigidity.SparseCohenFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealValue
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet alphabet mem_alphabet bitSet_injective)
open CohenGroundPoset InternalCohenProjectedGeneric InternalCohenRestriction InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem union_real (K a : ZFSet.{0}) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K)))
    (hfun : FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G)) :
    ∃ A : Oracle, ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
  classical
  have hn (n : ℕ) : ZFSet.pair a (natSet n) ∈ ZFSet.prod K ZFSet.omega :=
    ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hex (n : ℕ) : ∃ b : Bool,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G := by
    obtain ⟨b,hb,hnb,_⟩ := hfun.2 _ (hn n)
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    exact ⟨b,hnb⟩
  let A : Oracle := fun n => (hex n).choose
  refine ⟨A,fun n b => ⟨fun hb => ?_,fun he => he ▸ (hex n).choose_spec⟩⟩
  obtain ⟨v,hv,hnv,huniq⟩ := hfun.2 _ (hn n)
  exact bitSet_injective ((huniq _ ((mem_alphabet _).mpr ⟨A n,rfl⟩)
    (hex n).choose_spec).trans (huniq _ ((mem_alphabet _).mpr ⟨b,rfl⟩) hb).symm)

theorem val_realName (K a : ZFSet.{0}) (G : GenericFilter (Conditions (poset K)))
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    (realName K a).val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (poset K)) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M (poset K) G.carrier := by
  obtain ⟨A,hA⟩ := union_real K a ha G (CohenGenericUnion.manyColumn_union M K hM hT hK G hG).2
  have hv := val_realName K a G A hA
  exact ⟨A,hv,hA,(mem_extensionSet M (poset K) _ _).mpr
    ⟨realName K a,realName_internal M K a hM hT hK ha,hv⟩⟩

theorem singleton_filter_iff (a : ZFSet.{0})
    (G : GenericFilter (Conditions (poset {a}))) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b)
    (p : Conditions (poset {a})) :
    p ∈ G.carrier ↔ ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b := by
  rw [SparseCohenFilter.mem_filter_iff_subset_union]
  constructor
  · intro hp n b hb
    exact (hA n b).mp (hp hb)
  · intro hp z hz
    have hsub := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions (ZFSet.prod {a} ZFSet.omega) _).mp (label_mem _ p)).1).1
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
    obtain ⟨a',ha',n,hn,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain rfl := ZFSet.mem_singleton.mp ha'
    obtain ⟨n,rfl⟩ := (mem_omega _).mp hn
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    exact (hA n b).mpr (hp n b hz)

theorem pair_mem_projected_union (C B : ZFSet.{0}) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (x : ZFSet.{0}) (hx : x ∈ B) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ unionGraph (projected C B hBC G) ↔
      ZFSet.pair x (bitSet b) ∈ unionGraph G := by
  rw [InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨q,hq,hbit⟩
    obtain ⟨p,hp,rfl⟩ := (mem_projected C B hBC G q).mp hq
    rw [label_project,pair_restrict] at hbit
    exact ⟨p,hp,hbit.1⟩
  · rintro ⟨p,hp,hbit⟩
    refine ⟨project C B hBC p,projected_contains C B hBC G hp,?_⟩
    rw [label_project,pair_restrict]
    exact ⟨hbit,hx,(mem_alphabet _).mpr ⟨b,rfl⟩⟩

theorem projected_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ A : Oracle,
      (realName {a} a).val (projected C B hBC G).carrier = realCode A ∧
      (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      (∀ p : Conditions (poset {a}), p ∈ (projected C B hBC G).carrier ↔ ∀ n b,
        ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b) := by
  intro C B hBC
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A,hv,hA,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) (projected C B hBC G)
    (projected_groundGeneric M C B hM hT hC hB hBC G hG)
  have hfull (n : ℕ) (b : Bool) :
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
    rw [←pair_mem_projected_union C B hBC G _
      (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,(mem_omega _).mpr ⟨n,rfl⟩⟩) b]
    exact hA n b
  exact ⟨A,hv,val_realName K a G A hfull,hfull,
    singleton_filter_iff a (projected C B hBC G) A hA⟩

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNameEvaluation
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalNameEvaluation
open TransitiveNameModel RecursiveNames RelationCollapse
universe u

theorem activeRelation_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d g : ZFSet.{u}} (hd : d ∈ M) (hg : g ∈ M) : activeRelation d g ∈ M := by
  simpa only [activeRelation,activeFormula,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded activeFormula (cons d (fun _ => g))
      (by intro i; cases i <;> assumption)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hd hd)

theorem value_eq (d : ZFSet.{u}) (hd : Transitive d) {c : ZFSet.{u}}
    (G : Set (Conditions c)) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) :
    value d (activeRelation d (genericFilterSet c G)) (active_wellFounded _ _) (a.encode (label c)) = a.val G := by
  induction a with
  | mk ι child tag ih =>
    have hc (i : ι) : (child i).encode (label c) ∈ d := by
      have hp := hd _ ha _ (ZFSet.mem_range_self i)
      have hs := hd _ hp _ (ZFSet.mem_pair.mpr (Or.inl rfl))
      exact hd _ hs _ (ZFSet.mem_singleton.mpr rfl)
    apply ZFSet.ext; intro z
    rw [mem_value,Name.mem_val]
    constructor
    · rintro ⟨x,_,hxy,hzx⟩
      obtain ⟨_,_,p,hp,hpa⟩ := (active_pair _ _ _ _).mp hxy
      obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hpa
      obtain ⟨hiX,hiP⟩ := ZFSet.pair_inj.mp hi
      obtain ⟨q,hq,hqp⟩ := (mem_genericFilterSet c G p).mp hp
      have htag : tag i = q := label_injective c (hiP.trans hqp.symm)
      refine ⟨i,htag.symm ▸ hq,?_⟩
      rw [←ih i (hc i),hiX]
      exact hzx.symm
    · rintro ⟨i,hig,hiz⟩
      refine ⟨(child i).encode (label c),hc i,?_,?_⟩
      · exact (active_pair _ _ _ _).mpr ⟨hc i,ha,label c (tag i),
          (mem_genericFilterSet c G _).mpr ⟨tag i,hig,rfl⟩,ZFSet.mem_range_self i⟩
      · exact hiz.symm.trans (ih i (hc i)).symm

theorem name_value_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (G : Set (Conditions c)) (hg : genericFilterSet c G ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) : a.val G ∈ M := by
  obtain ⟨d,hdM,hd,had⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ha
  obtain ⟨f,hf,hfg⟩ := internal_graph M d (activeRelation d (genericFilterSet c G)) hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM (activeRelation_mem M hM hT hdM hg) (active_wellFounded _ _)
  have hp : ZFSet.pair (a.encode (label c))
      (value d (activeRelation d (genericFilterSet c G)) (active_wellFounded _ _) (a.encode (label c))) ∈ f :=
    (hfg.mem_iff (active_wellFounded _ _) _).mpr ⟨_,had,rfl⟩
  have hv := second_mem_doubleUnion hp
  have hi := hM _ (iterUnion_mem M hM hT.union hf 2) _ hv
  rwa [value_eq d hd G a had] at hi

theorem extension_subset (M N : ZFSet.{u}) (hN : Transitive N) (hT : SourceT N) (hMN : M ⊆ N)
    {c : ZFSet.{u}} (G : Set (Conditions c)) (hG : genericFilterSet c G ∈ N) :
    genericExtensionSet M c G ⊆ N := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G x).mp hx
  exact name_value_mem N hN hT G hG a (hMN ha)

end TuringRigidity.BoundedSetTheory.InternalNameEvaluation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem decision_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : decision c U ∈ M :=
  binary_union_mem M hM hT.pairing hT.union hU (neg_mem M c U hM hT hc hU)

theorem decision_dense (c U : ZFSet.{0}) (hUc : U ⊆ c) :
    Dense {p : Conditions c | label c p ∈ decision c U} := by
  classical
  intro p
  by_cases h : ∃ q ∈ U, label c p ⊆ q
  · obtain ⟨q,hq,hpq⟩ := h
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact ⟨q,hpq,ZFSet.mem_union.mpr (Or.inl hq)⟩
  · refine ⟨p,le_rfl,ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sep.mpr ⟨label_mem c p,?_⟩))⟩
    intro q hq hpq
    exact h ⟨q,hq,hpq⟩

theorem generic_decision (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hUc : U ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G U ∨ Hit G (neg c U) := by
  obtain ⟨p,hp,hpd⟩ := hG (decision c U) (decision_mem M c U hM hT hc hU) (decision_dense c U hUc)
  rcases ZFSet.mem_union.mp hpd with h | h
  · exact Or.inl ⟨p,hp,h⟩
  · exact Or.inr ⟨p,hp,h⟩

end TuringRigidity.InternalBooleanGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeRecovery InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_properties (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let N := genericExtensionSet M c G.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ genericFilterSet c G.carrier ∈ N := by
  let _ : Top (Conditions c) := ⟨Classical.choose G.nonempty⟩
  have ht : ⊤ ∈ G.carrier := Classical.choose_spec G.nonempty
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
      (InternalCollapse.orderSet_pair c) G hG ht,
    ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht,
    genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht⟩

end TuringRigidity.RegularTreeExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalDenseInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalDenseInclusion
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem densePull_mem (M a b D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) : densePull a b D ∈ M := by
  let e := cons b (fun _ => D)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hb; exact hD
  simpa only [densePull,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.member 0 3) (.subset 0 1))) e he ha

end TuringRigidity.InternalDenseInclusion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixDensity
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPrefixDensity
open TransitiveNameModel BoundedSetTheory InternalCohen CohenConditionCode InternalFiniteSubsets
attribute [local instance] InternalCollapse.order

theorem condition_extends_prefix (q : ZFSet.{0})
    (hq : q ∈ CohenGroundPoset.conditions ZFSet.omega) :
    ∃ s : List Bool, q ⊆ wordCode s := by
  classical
  obtain ⟨p,rfl⟩ := (isCondition_iff_graph _ q).mp ((CohenGroundPoset.mem_conditions _ _).mp hq)
  let f (n : ℕ) : Conditions ZFSet.omega :=
    equivShrink _ ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hfl (n : ℕ) : label ZFSet.omega (f n) = natSet n := by simp [f,label]
  have hfi : Function.Injective f := by
    intro n m h
    exact natSet_injective (by simpa only [hfl] using congrArg (label ZFSet.omega) h)
  have hfin := p.finite.preimage hfi.injOn
  obtain ⟨n,hn⟩ := hfin.bddAbove
  let s := List.ofFn (fun i : Fin (n+1) => (p.val (f i.val)).getD false)
  refine ⟨s,?_⟩
  intro z hz
  obtain ⟨i,b,hib,rfl⟩ := (mem_graph _ p z).mp hz
  obtain ⟨k,hk⟩ := (mem_omega _).mp (label_mem ZFSet.omega i)
  have he : i = f k := label_injective _ (hk.trans (hfl k).symm)
  have hkb : p.val (f k) = some b := he ▸ hib
  have hkn : k < n+1 := Nat.lt_succ_of_le (hn (by
    change p.val (f k) ≠ none
    simp [hkb]))
  rw [he,hfl]
  apply (pair_mem_wordCode s k b).mpr
  refine ⟨by simpa only [s,List.length_ofFn] using hkn,?_⟩
  simp only [s,List.getElem_ofFn,hkb,Option.getD_some]

end TuringRigidity.CohenPrefixDensity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenPrefixGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalCohen (bitSet wordCode pair_mem_wordCode)
open CohenBorelForcing ShuffleRequirements InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem prefix_dense_expansion (D : ZFSet.{0})
    (hD : Dense {p : Conditions InternalCohen.conditions | label _ p ∈ D}) :
    Dense {q : Conditions poset | label _ q ∈ densePull poset InternalCohen.conditions D} := by
  intro p
  obtain ⟨s,hs⟩ := CohenPrefixDensity.condition_extends_prefix _ (label_mem poset p)
  let u : Conditions InternalCohen.conditions := InternalCohen.conditionEquiv ⟨s⟩
  have hu : label _ u = wordCode s := InternalCohen.label_encodeCondition ⟨s⟩
  obtain ⟨q,hqu,hqD⟩ := hD u
  let r := embed InternalCohen.conditions poset CohenPrefixDensity.conditions_subset q
  have hr : label poset r = label InternalCohen.conditions q := label_embed _ _ _ q
  refine ⟨r,?_,?_⟩
  · change label poset p ⊆ label poset r
    rw [hr]
    exact fun z hz => hqu (hu.symm ▸ hs hz)
  · apply ZFSet.mem_sep.mpr
    exact ⟨label_mem poset r,label _ q,label_mem _ q,hqD,by rw [hr]⟩

theorem prefix_ground_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ InternalCollapse.unionGraph G ↔ A n = b) :
    AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A)) := by
  intro D hDM hD
  have hc := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hp := InternalCohen.conditions_mem M hM hT
  obtain ⟨q,hq,hqD⟩ := hG (densePull poset InternalCohen.conditions D)
    (densePull_mem M poset InternalCohen.conditions D hM hT hc hp hDM)
    (prefix_dense_expansion D hD)
  obtain ⟨_,p,hp,hpD,hpq⟩ := ZFSet.mem_sep.mp hqD
  obtain ⟨s,rfl⟩ := (InternalCohen.prefix_iff_wordCode p).mp ((InternalCohen.mem_conditions p).mp hp)
  let t : Conditions InternalCohen.conditions := InternalCohen.conditionEquiv ⟨s⟩
  refine ⟨t,?_,?_⟩
  · have hreal : Realizes s A := by
      intro n hn
      have hb := (hA n s[n]).mp ((InternalCollapse.mem_unionGraph G _).mpr
        ⟨q,hq,hpq ((pair_mem_wordCode s n s[n]).mpr ⟨hn,rfl⟩)⟩)
      simpa only [List.getD,List.getElem?_eq_getElem hn,Option.getD_some] using hb.symm
    simpa only [t,InternalCohen.pushFilter,InternalCohen.conditionEquiv.symm_apply_apply,
      realFilter,Set.mem_ofPred_eq] using hreal
  · change label _ (InternalCohen.encodeCondition ⟨s⟩) ∈ D
    rwa [InternalCohen.label_encodeCondition]

end TuringRigidity.SparseCohenRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DenseInclusionExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.DenseInclusionExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem restrictSet_mem (N a k : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (ha : a ∈ N) (hk : k ∈ N) : restrictSet a k ∈ N := by
  let e := fun _ : ℕ => k
  simpa only [restrictSet,Formula.Eval,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded (.member 0 1) e (fun _ => hk) ha

end TuringRigidity.DenseInclusionExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrderIsoTransport
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalOrderIsoTransport
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem preimageSet_mem (M a f k : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hf : f ∈ M) (hk : k ∈ M) : preimageSet a f k ∈ M := by
  let e := cons k (fun _ => f)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hk; exact hf
  simpa only [preimageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 1 0 3)) e he ha

theorem map_ground_generic (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (AutomorphismName.mapFilter e G) := by
  intro D hD hd
  let E := DenseInclusionExtension.restrictSet b D
  have hE := DenseInclusionExtension.restrictSet_mem M b D hM hT hb hD
  have hden : Dense {p : Conditions a | label a p ∈ preimageSet a f E} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hd (e p)
    refine ⟨e.symm q,by simpa using e.symm.monotone hqp,?_⟩
    exact ZFSet.mem_sep.mpr ⟨label_mem a _,label b q,ZFSet.mem_sep.mpr ⟨label_mem b q,hqD⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  obtain ⟨p,hp,hpD⟩ := hG (preimageSet a f E) (preimageSet_mem M a f E hM hT ha hf hE) hden
  obtain ⟨_,y,hyD,hpy⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨hyb,hyD⟩ := ZFSet.mem_sep.mp hyD
  obtain ⟨q,rfl⟩ := label_surjective b hyb
  obtain rfl := (he p q).mp hpy
  exact ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,hyD⟩

end TuringRigidity.InternalOrderIsoTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalGraphEquiv
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalGraphEquiv
open TransitiveNameModel BoundedSetTheory

theorem graphEquiv_spec (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) (x : Conditions A) (y : Conditions B) :
    ZFSet.pair (label A x) (label B y) ∈ f ↔ y = graphEquiv A B f hf hi hs x := by
  exact ⟨fun h => label_injective B (hf.functional (label_mem A x) h (graphMap_spec A B f hf x)),
    fun h => h.symm ▸ graphMap_spec A B f hf x⟩

end TuringRigidity.InternalGraphEquiv

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenReindex
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenReindex
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem matchesFormula_spec (A B f p q bit : ℕ) (e : ℕ → ZFSet.{0}) (hb : e bit = alphabet) :
    (matchesFormula A B f p q bit).Eval e ↔ Matches (e A) (e B) (e f) (e p) (e q) := by
  simp only [Matches,matchesFormula,Formula.eval_allMem,Formula.eval_imp,Formula.eval_iff,
    Formula.eval_pairMem,cons_zero,cons_succ,hb]

theorem matches_graph_iff (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Condition (Conditions A)) (q : Condition (Conditions B)) :
    Matches A B f (graph A p) (graph B q) ↔ q = CohenCoordinates.reindex e p := by
  constructor
  · intro h
    apply Condition.ext; funext j
    apply Option.ext; intro b
    have hh := h (label A (e.symm j)) (label_mem _ _) (label B j) (label_mem _ _)
      ((he _ _).mpr (e.apply_symm_apply j).symm) (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)
    rw [pair_mem_graph,pair_mem_graph] at hh
    exact hh.symm
  · rintro rfl x hx y hy hxy b hb
    obtain ⟨i,rfl⟩ := label_surjective A hx
    obtain ⟨j,rfl⟩ := label_surjective B hy
    obtain rfl := (he i j).mp hxy
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    rw [pair_mem_graph,pair_mem_graph]
    change p.val i = some b ↔ p.val (e.symm (e i)) = some b
    rw [e.symm_apply_apply]

theorem pair_reindexGraph (A B f p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ reindexGraph A B f ↔ p ∈ conditions A ∧ q ∈ conditions B ∧ Matches A B f p q := by
  simp only [reindexGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,h⟩
  · rintro ⟨hp,hq,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,h⟩

theorem reindexGraph_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : reindexGraph A B f ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons A (cons B (cons f (fun _ => alphabet)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hcA; exact hcB; exact hA; exact hB; exact hf; exact InternalCohen.alphabet_mem M hM hT
  have hmatches (pairValue leftCondition rightCondition : ZFSet.{0}) :
      (matchesFormula 5 6 7 1 0 8).Eval
        (cons rightCondition (cons leftCondition (cons pairValue e))) ↔
        Matches A B f leftCondition rightCondition :=
    matchesFormula_spec 5 6 7 1 0 8 _ rfl
  simpa only [reindexGraph,Formula.Eval,Formula.eval_orderedPair,hmatches,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (matchesFormula 5 6 7 1 0 8)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)

theorem reindexGraph_spec (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Conditions (conditions A)) (q : Conditions (conditions B)) :
    ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = reindexIso A B e p := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv B).surjective q
  rw [pair_reindexGraph]
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv B q) = graph B q := label_encode B q
  rw [and_iff_right (label_mem _ _),and_iff_right (label_mem _ _),hp,hq,matches_graph_iff A B f e he]
  change q = CohenCoordinates.reindex e p ↔
    conditionEquiv B q = conditionEquiv B (CohenCoordinates.reindex e ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv B).injective.eq_iff.symm

theorem internal_reindex (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hfM : f ∈ M) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    ∃ e : Conditions (conditions A) ≃o Conditions (conditions B),
      reindexGraph A B f ∈ M ∧
      (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = e p) ∧
      conditions A ∈ M ∧ InternalCollapse.orderSet (conditions A) ∈ M ∧
      conditions B ∈ M ∧ InternalCollapse.orderSet (conditions B) ∈ M := by
  let e := InternalGraphEquiv.graphEquiv A B f hf hi hs
  exact ⟨reindexIso A B e,reindexGraph_mem M A B f hM hT hA hB hfM,
    reindexGraph_spec A B f e (InternalGraphEquiv.graphEquiv_spec A B f hf hi hs),
    (poset_internal M A hM hT hA).1,(poset_internal M A hM hT hA).2,
    poset_internal M B hM hT hB⟩

end TuringRigidity.InternalCohenReindex

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSingletonColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSingletonColumn
open TransitiveNameModel BoundedSetTheory CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem pair_graph (a W u n : ZFSet.{0}) :
    ZFSet.pair u n ∈ graph a W ↔ n ∈ W ∧ u = ZFSet.pair a n := by
  constructor
  · intro h
    obtain ⟨_,v,_,m,hm,he,hv⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hm,hv⟩
  · rintro ⟨hn,hu⟩
    have huA : u ∈ ZFSet.prod {a} W := hu ▸ ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨huA,hn⟩,u,huA,n,hn,rfl,hu⟩

theorem graph_mem (M a W : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hW : W ∈ M) : graph a W ∈ M := by
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hW
  let e := cons (ZFSet.prod {a} W) (cons W (fun _ => a))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hA; exact hW; exact ha
  simpa only [graph,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.orderedPair 1 5 0)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hW)

theorem graph_function (a W : ZFSet.{0}) : FunctionGraph (ZFSet.prod {a} W) W (graph a W) := by
  refine ⟨fun z hz => ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1,?_⟩
  intro u hu
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hu
  have hx_eq : x = a := ZFSet.mem_singleton.mp hx
  subst x
  exact ⟨n,hn,(pair_graph a W _ n).mpr ⟨hn,rfl⟩,fun m _ hm =>
    (ZFSet.pair_inj.mp ((pair_graph a W _ m).mp hm).2).2.symm⟩

theorem graph_injective (a W : ZFSet.{0}) :
    ∀ x ∈ ZFSet.prod {a} W, ∀ x' ∈ ZFSet.prod {a} W, ∀ y ∈ W,
      ZFSet.pair x y ∈ graph a W → ZFSet.pair x' y ∈ graph a W → x = x' := by
  intro x _ x' _ y _ hx hx'
  exact ((pair_graph a W x y).mp hx).2.trans ((pair_graph a W x' y).mp hx').2.symm

theorem graph_onto (a W : ZFSet.{0}) :
    ∀ y ∈ W, ∃ x ∈ ZFSet.prod {a} W, ZFSet.pair x y ∈ graph a W := by
  intro y hy
  exact ⟨ZFSet.pair a y,ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hy⟩,
    (pair_graph a W _ y).mpr ⟨hy,rfl⟩⟩

end TuringRigidity.InternalSingletonColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnPrefixGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenProjectedGeneric AutomorphismName
open InternalCohen (bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem singleton_iso_bits (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) :
    ∃ e : Conditions (poset {a}) ≃o Conditions SparseCohenRealName.poset,
      ∃ f ∈ M,
        (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p) ∧
        ∀ p n b, ZFSet.pair (natSet n) (bitSet b) ∈ label _ (e p) ↔
          ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p := by
  let B := ZFSet.prod {a} ZFSet.omega
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (singleton_mem M hM hT.pairing ha) hω
  obtain ⟨e,hf,he,_⟩ := InternalCohenReindex.internal_reindex M B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) hM hT hB hω
    (InternalSingletonColumn.graph_mem M a ZFSet.omega hM hT ha hω)
    (InternalSingletonColumn.graph_function a ZFSet.omega)
    (InternalSingletonColumn.graph_injective a ZFSet.omega)
    (InternalSingletonColumn.graph_onto a ZFSet.omega)
  refine ⟨e,_,hf,he,fun p n b => ?_⟩
  have hn : natSet n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have hm := ((InternalCohenReindex.pair_reindexGraph B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) _ _).mp ((he p (e p)).mpr rfl)).2.2
  exact (hm _ (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩) _ hn
    ((InternalSingletonColumn.pair_graph a ZFSet.omega _ _).mpr ⟨hn,rfl⟩)
    (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)).symm

theorem selected_real_prefix_generic (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle) (hv : (realName K a).val G.carrier = realCode A) :
    AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter A)) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := ZFSet.prod {a} ZFSet.omega
  let hBC := singleton_coordinates_subset K a ha
  let H := projected C B hBC G
  have haM := hM K hK a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  have hH := projected_groundGeneric M C B hM hT hC hB hBC G hG
  obtain ⟨AH,hvH,hbits,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) H hH
  obtain ⟨AG,hvGH,hvG,_,_⟩ := projected_real_value M K a hM hT hK ha G hG
  have hAG : AG = A := realCode_injective (hvG.symm.trans hv)
  have hAH : AH = AG := realCode_injective (hvH.symm.trans hvGH)
  subst AG; subst AH
  obtain ⟨e,f,hf,he,hbit⟩ := singleton_iso_bits M a hM hT haM
  let L := mapFilter e H
  have hL := InternalOrderIsoTransport.map_ground_generic M (poset {a}) SparseCohenRealName.poset f
    hM hT (conditions_mem M B hM hT hB)
    (conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)) hf e he H hH
  apply SparseCohenRealName.prefix_ground_generic M hM hT L hL A
  intro n b
  rw [←hbits n b,InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨p,hp,hpb⟩
    refine ⟨e.symm p,hp,?_⟩
    exact (hbit (e.symm p) n b).mp (by simpa only [e.apply_symm_apply] using hpb)
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e p,by simpa only [L,mapFilter,Set.mem_ofPred_eq,e.symm_apply_apply] using hp,
      (hbit p n b).mpr hpb⟩

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFreshColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFreshColumn
open TransitiveNameModel BoundedSetTheory InternalCountableOrdinals InternalCountableClosure
open CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem product_difference (K C W : ZFSet.{0}) :
    ZFSet.prod K W \ ZFSet.prod C W = ZFSet.prod (K \ C) W := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨hzK,hzC⟩ := ZFSet.mem_sdiff.mp hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hzK
    exact ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_sdiff.mpr ⟨hx,fun h =>
      hzC (ZFSet.pair_mem_prod.mpr ⟨h,hn⟩)⟩,hn⟩
  · intro hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨hxK,hxC⟩ := ZFSet.mem_sdiff.mp hx
    exact ZFSet.mem_sdiff.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hxK,hn⟩,
      fun h => hxC (ZFSet.pair_mem_prod.mp h).1⟩

end TuringRigidity.CohenFreshColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealGeneratedModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedModel
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalBooleanTop

theorem mem_hull (M X z : ZFSet.{0}) (h : ∃ N, Contains M X N) :
    z ∈ hull M X ↔ ∀ N, Contains M X N → z ∈ N := by
  rw [hull,dite_eq_left h,ZFSet.mem_sep]
  exact ⟨fun hz => hz.2,fun hz => ⟨hz h.choose h.choose_spec,hz⟩⟩

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

end TuringRigidity.RealGeneratedModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFactorRequirement
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFactorRequirement
open TransitiveNameModel BoundedSetTheory CohenGroundPoset
open InternalCohenFactor InternalCohenRestriction InternalCohenPartition
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem requirement_mem (M A B R : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hR : R ∈ M) : requirement A B R ∈ M := by
  have hD := complement_mem M A B hM hT hA hB
  let e := cons (conditions B) (cons (conditions (A \ B))
    (cons (restrictionGraph A B) (cons (restrictionGraph A (A \ B)) (fun _ => R))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact conditions_mem M B hM hT hB
    exact conditions_mem M _ hM hT hD
    exact restrictionGraph_mem M A B hM hT hA hB
    exact restrictionGraph_mem M A _ hM hT hA hD
    exact hR
  simpa only [requirement,Formula.Eval,Formula.eval_pairMem,Formula.eval_subset,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 4)
        (.existsMem 3 (.conj (.pairMem 2 0 6)
          (.existsMem 4 (.conj (.subset 0 1)
            (.existsMem 4 (.conj (.subset 0 3) (.pairMem 1 0 9))))))))) e he
      (conditions_mem M A hM hT hA)

theorem label_requirement (A B R : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) :
    label _ p ∈ requirement A B R ↔
      ∃ r : Conditions (conditions (A \ B)), ∃ a : Conditions (conditions B),
        project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p ≤ r ∧
        project A B hBA p ≤ a ∧ ZFSet.pair (label _ r) (label _ a) ∈ R := by
  rw [requirement,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,b,_,hb,d,_,hd,r,hr,hrd,a,ha,hab,hra⟩
    obtain ⟨r,rfl⟩ := label_surjective _ hr
    obtain ⟨a,rfl⟩ := label_surjective _ ha
    have hb' := ((pair_restrictionGraph A B _ b).mp hb).2.2
    have hd' := ((pair_restrictionGraph A (A \ B) _ d).mp hd).2.2
    refine ⟨r,a,?_,?_,hra⟩
    · change label _ r ⊆ label _ (project A (A \ B) _ p)
      rw [label_project,←hd']; exact hrd
    · change label _ a ⊆ label _ (project A B _ p)
      rw [label_project,←hb']; exact hab
  · rintro ⟨r,a,hr,ha,hra⟩
    refine ⟨label_mem _ p,label _ (project A B hBA p),label_mem _ _,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,
      label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p),label_mem _ _,
      (pair_restrictionGraph A (A \ B) _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A _ _ p⟩,
      label _ r,label_mem _ r,hr,label _ a,label_mem _ a,ha,hra⟩

end TuringRigidity.CohenFactorRequirement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalColumnExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalColumnExtension
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem filterImage_mem (N A B g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hB : B ∈ N) (hg : g ∈ N) : filterImage A B g ∈ N := by
  have hR := restrictionGraph_mem N A B hN hT hA hB
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) (cons g (fun _ => restrictionGraph A B))
    (by intro i; cases i; exact hg; exact hR) (conditions_mem N B hN hT hB)
  simpa only [filterImage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using hs

theorem projected_filter_image (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) :
    genericFilterSet (conditions B) (projected A B hBA G).carrier =
      filterImage A B (genericFilterSet (conditions A) G.carrier) := by
  apply ZFSet.ext; intro q
  rw [mem_genericFilterSet,filterImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨p,hp,hps⟩ := (mem_projected A B hBA G s).mp hs
    refine ⟨label_mem _ s,label _ p,(mem_genericFilterSet _ _ _).mpr ⟨p,hp,rfl⟩,?_⟩
    rw [←hps]
    exact (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩
  · rintro ⟨hq,p,hp,hpq⟩
    obtain ⟨r,hr,hrp⟩ := (mem_genericFilterSet (conditions A) G.carrier p).mp hp
    rw [←hrp] at hpq
    have he := ((pair_restrictionGraph A B _ q).mp hpq).2.2
    refine ⟨project A B hBA r,projected_contains A B hBA G hr,?_⟩
    exact (label_project A B hBA r).trans he.symm

theorem column_extension_subset (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M (conditions B) (projected A B hBA G).carrier ⊆
      genericExtensionSet M (conditions A) G.carrier := by
  let N := genericExtensionSet M (conditions A) G.carrier
  have hN := genericExtensionSet_transitive M (conditions A) hM G.carrier
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  have hc := conditions_mem M A hM hT hA
  have hTN : SourceT N := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) G hG ht
  have hMN : M ⊆ N := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  rw [projected_filter_image A B hBA G]
  apply filterImage_mem N A B _ hN hTN (hMN hA) (hMN hB)
  exact genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht

end TuringRigidity.InternalColumnExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenUntouchedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenUntouchedGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open CohenGroundPoset InternalCohenFactor InternalCohenPartition InternalCohenProjectedGeneric
open CohenFactorRequirement
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem meets_named_dense (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
    (hD : Dense {p : Conditions (conditions (A \ B)) |
      label _ p ∈ τ.val (projected A B hBA G).carrier}) :
    ∃ r ∈ (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G).carrier,
      label _ r ∈ τ.val (projected A B hBA G).carrier := by
  let J := projected A B hBA G
  let hDA : A \ B ⊆ A := fun _ h => (ZFSet.mem_sdiff.mp h).1
  let L := projected A (A \ B) hDA G
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hDM := complement_mem M A B hM hT hA hB
  have hcD := conditions_mem M (A \ B) hM hT hDM
  have ho := InternalCollapse.orderSet_mem M hM hT hcB
  have hJ : GroundGeneric M J := projected_groundGeneric M A B hM hT hA hB hBA G hG
  obtain ⟨a₀,ha₀⟩ := J.nonempty
  have hJt : ⊤ ∈ J.carrier := J.upper le_top ha₀
  let R := CheckedForcingRelation.relation (conditions (A \ B)) τ
  have hRM : R ∈ M := CheckedForcingRelation.relation_mem M _ hM hT hcB hcD ho
    (InternalCollapse.orderSet_pair _) τ hτ
  have truth (r : Conditions (conditions (A \ B))) : label _ r ∈ τ.val J.carrier ↔
      ∃ a ∈ J.carrier, MemForces (Name.check (label _ r)) τ a := by
    have hcheck := encoded_check_mem M (conditions B) hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB
      (hM _ hcD _ (label_mem _ r))
    have h := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB
      ho (InternalCollapse.orderSet_pair _) J hJ (Name.check (label _ r)) τ hcheck hτ).2
    simpa only [Name.val_check _ hJt] using h
  let U := requirement A B R
  have hUM := requirement_mem M A B R hM hT hA hB hRM
  rcases InternalBooleanGeneric.generic_decision M (conditions A) U hM hT hcA hUM
    (fun _ h => (ZFSet.mem_sep.mp h).1) G hG with hU|hn
  · obtain ⟨p,hp,hpU⟩ := hU
    obtain ⟨r,a,hpr,hpa,hra⟩ := (label_requirement A B R hBA p).mp hpU
    have hrL : r ∈ L.carrier := L.upper hpr (projected_contains A (A \ B) hDA G hp)
    have haJ : a ∈ J.carrier := J.upper hpa (projected_contains A B hBA G hp)
    exact ⟨r,hrL,(truth r).mpr ⟨a,haJ,
      ((CheckedForcingRelation.pair_relation _ _ τ a).mp hra).2⟩⟩
  · obtain ⟨p,hp,hpn⟩ := hn
    obtain ⟨r,hrp,hrD⟩ := hD (project A (A \ B) hDA p)
    obtain ⟨a,ha,hforce⟩ := (truth r).mp hrD
    obtain ⟨b,_,hba,hbp⟩ := J.directed ha (projected_contains A B hBA G hp)
    let e := factorIso A B hBA
    let s := e.symm (b,r)
    have hs : e s = (b,r) := e.apply_symm_apply _
    have hsb : project A B hBA s = b := congrArg Prod.fst hs
    have hsr : project A (A \ B) hDA s = r := congrArg Prod.snd hs
    have hsp : s ≤ p := e.le_iff_le.mp (by rw [hs]; exact ⟨hbp,hrp⟩)
    have hsU : label _ s ∈ U := by
      apply (label_requirement A B R hBA s).mpr
      refine ⟨r,a,?_,?_,(CheckedForcingRelation.pair_relation _ _ τ a).mpr ⟨label_mem _ r,hforce⟩⟩
      · rw [hsr]
      · rw [hsb]; exact hba
    exact False.elim ((ZFSet.mem_sep.mp hpn).2 (label _ s) hsU hsp)

theorem untouched_ground_generic (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G) :
    GroundGeneric (genericExtensionSet M (conditions B) (projected A B hBA G).carrier)
      (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G) := by
  intro D hDN hD
  obtain ⟨τ,hτ,hval⟩ := (mem_extensionSet _ _ _ D).mp hDN
  have hd := hD
  rw [←hval] at hd
  obtain ⟨r,hr,hrD⟩ := meets_named_dense M A B hM hT hA hB hBA G hG τ hτ hd
  exact ⟨r,hr,hval ▸ hrD⟩

end TuringRigidity.CohenUntouchedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenDisjointPrefixPair
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.CohenDisjointPrefixPair
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_pair_oai (M K a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (hb : b ∈ K) (hab : b ≠ a)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet M InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := ZFSet.prod {a} ZFSet.omega
  have hBC : B ⊆ C := singleton_coordinates_subset K a ha
  have hω := sourceT_omega_mem M hM hT
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC : C ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hB : B ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle hω
  let J := projected C B hBC G
  have hJ : GroundGeneric M J := projected_groundGeneric M C B hM hT hC hB hBC G hG
  let N := genericExtensionSet M (poset {a}) J.carrier
  obtain ⟨hN,hTN,hMN,_⟩ := RegularTreeExtension.extension_properties M (poset {a}) hM hT
    (CohenGroundPoset.conditions_mem M B hM hT hB) J hJ
  obtain ⟨L,hLv,_,hLN⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) J hJ
  have hL := selected_real_prefix_generic M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) J hJ L hLv
  have hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier :=
    InternalColumnExtension.column_extension_subset M C B hM hT hC hB hBC G hG hLN
  have hrem : K \ {a} ∈ M := InternalCohenPartition.complement_mem M K {a} hM hT hK hsingle
  have hbrem : b ∈ K \ {a} := ZFSet.mem_sdiff.mpr ⟨hb,fun h => hab (ZFSet.mem_singleton.mp h)⟩
  have hsecond : ∃ U : GenericFilter (Conditions (poset (K \ {a}))),
      GroundGeneric N U ∧ genericExtensionSet M (poset (K \ {a})) U.carrier ⊆
        genericExtensionSet M (poset K) G.carrier := by
    have hDC : C \ B ⊆ C := fun _ h => (ZFSet.mem_sdiff.mp h).1
    have hD := InternalCohenPartition.complement_mem M C B hM hT hC hB
    have hU := CohenUntouchedGeneric.untouched_ground_generic M C B hM hT hC hB hBC G hG
    have hUE := InternalColumnExtension.column_extension_subset M C (C \ B) hM hT hC hD hDC G hG
    let F (D : ZFSet.{0}) : Prop :=
      ∃ U : GenericFilter (Conditions (CohenGroundPoset.conditions D)),
        GroundGeneric N U ∧ genericExtensionSet M (CohenGroundPoset.conditions D) U.carrier ⊆
          genericExtensionSet M (poset K) G.carrier
    have hF : F (C \ B) := ⟨projected C (C \ B) hDC G,hU,hUE⟩
    exact (congrArg F (CohenFreshColumn.product_difference K {a} ZFSet.omega)).mp hF
  obtain ⟨U,hUN,hUE⟩ := hsecond
  have hUM : GroundGeneric M U := fun D hD hd => hUN D (hMN hD) hd
  obtain ⟨R,hRv,_,hRMU⟩ := generic_real_value M (K \ {a}) b hM hT hrem hbrem U hUM
  have hRN := selected_real_prefix_generic N (K \ {a}) b hN hTN (hMN hrem) hbrem U hUN R hRv
  have hContains : RealGeneratedModel.Contains M (realCode L) N := ⟨hN,hTN,hMN,hLN⟩
  have hprefix : genericExtensionSet M InternalCohen.conditions
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier ⊆ N := by
    rw [InternalCohen.prefix_extension_eq_hull M hM hT L hL]
    intro z hz
    exact (RealGeneratedModel.mem_hull M (realCode L) z ⟨N,hContains⟩).mp hz N hContains
  exact ⟨L,R,hLE,hUE hRMU,hL,fun D hD hd => hRN D (hprefix hD) hd⟩

end TuringRigidity.CohenDisjointPrefixPair

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair_oai := @OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair_oai
