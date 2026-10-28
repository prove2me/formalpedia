-- Prove2me | solution 1 for OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:58:01.030496+00:00
-- url     : https://prove2.me/submissions/9f7f5078-2d96-42da-9a58-13095949b749

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_CohenAbsorptionGeneric_product_generic_absorption

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFactor
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenFactor
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenRestriction InternalCohenPartition
open InternalCohen (alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem factorGraph_pair (A B p q r : ZFSet.{0}) :
    ZFSet.pair p (ZFSet.pair q r) ∈ factorGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ r ∈ conditions (A \ B) ∧
        q = restrict B p ∧ r = restrict (A \ B) p := by
  simp only [factorGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,r',hr,he,hs⟩
    obtain ⟨hpEq,hqrEq⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hqEq,hrEq⟩ := ZFSet.pair_inj.mp hqrEq
    subst p'; subst q'; subst r'
    exact ⟨hp,hq,hr,hs⟩
  · rintro ⟨hp,hq,hr,hs⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,ZFSet.pair_mem_prod.mpr ⟨hq,hr⟩⟩,
      p,hp,q,hq,r,hr,rfl,hs⟩

theorem factorGraph_is_iso_graph (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A))
    (q : Conditions (conditions B)) (r : Conditions (conditions (A \ B))) :
    ZFSet.pair (label _ p) (ZFSet.pair (label _ q) (label _ r)) ∈ factorGraph A B ↔
      factorIso A B hBA p = (q,r) := by
  rw [factorGraph_pair]
  simp only [label_mem,true_and]
  constructor
  · intro h
    apply Prod.ext <;> apply label_injective
    · exact (label_project A B hBA p).trans h.1.symm
    · exact (label_project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p).trans h.2.symm
  · intro h
    have hq := congrArg (fun t => label (conditions B) t.1) h
    have hr := congrArg (fun t => label (conditions (A \ B)) t.2) h
    exact ⟨hq.symm.trans (label_project A B hBA p),hr.symm.trans (label_project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p)⟩

theorem factor_internal (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) :
    conditions B ∈ M ∧ conditions (A \ B) ∈ M ∧
      InternalCollapse.orderSet (conditions B) ∈ M ∧
      InternalCollapse.orderSet (conditions (A \ B)) ∈ M ∧ factorGraph A B ∈ M := by
  have hD := complement_mem M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hcD := conditions_mem M (A \ B) hM hT hD
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcB hcD
  refine ⟨hcB,hcD,InternalCollapse.orderSet_mem M hM hT hcB,
    InternalCollapse.orderSet_mem M hM hT hcD,?_⟩
  let e := cons (conditions A) (cons (conditions B) (cons (conditions (A \ B))
    (cons (productCode A B) (cons B (cons (A \ B) (fun _ => alphabet))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|i
    exact hcA; exact hcB; exact hcD; exact hprod; exact hB; exact hD
    exact InternalCohen.alphabet_mem M hM hT
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 5
    (.existsMem 7 (.conj (.orderedPair 0 2 1) (.conj (.orderedPair 4 3 0)
      (.conj (restrictionFormula 9 11 3 2) (restrictionFormula 10 11 3 1)))))))
  have hs₁ (z p q r t : ZFSet.{0}) := restrictionFormula_spec 9 11 3 2
    (cons t (cons r (cons q (cons p (cons z e))))) rfl
  have hs₂ (z p q r t : ZFSet.{0}) := restrictionFormula_spec 10 11 3 1
    (cons t (cons r (cons q (cons p (cons z e))))) rfl
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ p ∈ conditions A, ∃ q ∈ conditions B, ∃ r ∈ conditions (A \ B),
        z = ZFSet.pair p (ZFSet.pair q r) ∧ q = restrict B p ∧ r = restrict (A \ B) p := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,hs₁,hs₂,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨p,hp,q,hq,r,hr,t,_,ht,hz,hs⟩
      exact ⟨p,hp,q,hq,r,hr,ht ▸ hz,hs⟩
    · rintro ⟨p,hp,q,hq,r,hr,hz,hs⟩
      exact ⟨p,hp,q,hq,r,hr,ZFSet.pair q r,ZFSet.pair_mem_prod.mpr ⟨hq,hr⟩,rfl,hz,hs⟩
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hprod)
  simpa only [factorGraph,hφ,productCode] using hh

end TuringRigidity.InternalCohenFactor

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFactorReconstruction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFactorReconstruction
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenFactor InternalCohenPartition InternalCohenRestriction
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem mem_iff_projections (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (p : Conditions (conditions A)) :
    p ∈ G.carrier ↔ project A B hBA p ∈ (projected A B hBA G).carrier ∧
      project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p ∈
        (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G).carrier := by
  constructor
  · intro hp
    exact ⟨projected_contains A B hBA G hp,projected_contains A (A \ B) _ G hp⟩
  · rintro ⟨hb,hd⟩
    obtain ⟨b,hb,hbp⟩ := (mem_projected A B hBA G _).mp hb
    obtain ⟨d,hd,hdp⟩ := (mem_projected A (A \ B) _ G _).mp hd
    obtain ⟨s,hs,hsb,hsd⟩ := G.directed hb hd
    let e := factorIso A B hBA
    have h₁ := (e.monotone hsb).1
    have h₂ := (e.monotone hsd).2
    change project A B hBA s ≤ project A B hBA b at h₁
    change project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) s ≤
      project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) d at h₂
    rw [hbp] at h₁
    rw [hdp] at h₂
    exact G.upper (e.le_iff_le.mp ⟨h₁,h₂⟩) hs

theorem reconstruct_mem (N A B j l : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hB : B ∈ N) (hj : j ∈ N) (hl : l ∈ N) : reconstruct A B j l ∈ N := by
  have hD := complement_mem N A B hN hT hA hB
  let e := cons j (cons l (cons (restrictionGraph A B) (fun _ => restrictionGraph A (A \ B))))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i
    exact hj; exact hl
    exact restrictionGraph_mem N A B hN hT hA hB
    exact restrictionGraph_mem N A _ hN hT hA hD
  simpa only [reconstruct,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.pairMem 2 1 5) (.pairMem 2 0 6)))) e he
      (conditions_mem N A hN hT hA)

theorem reconstruct_filter (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) :
    reconstruct A B (genericFilterSet (conditions B) (projected A B hBA G).carrier)
      (genericFilterSet (conditions (A \ B))
        (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G).carrier) =
      genericFilterSet (conditions A) G.carrier := by
  apply ZFSet.ext; intro z
  rw [reconstruct,ZFSet.mem_sep,mem_genericFilterSet]
  constructor
  · rintro ⟨hz,b,hb,d,hd,hzb,hzd⟩
    obtain ⟨p,rfl⟩ := label_surjective _ hz
    obtain ⟨b,hbj,rfl⟩ := (mem_genericFilterSet _ _ b).mp hb
    obtain ⟨d,hdl,rfl⟩ := (mem_genericFilterSet _ _ d).mp hd
    have hbp : project A B hBA p = b := label_injective _
      ((label_project A B hBA p).trans ((pair_restrictionGraph A B _ _).mp hzb).2.2.symm)
    have hdp : project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p = d := label_injective _
      ((label_project A (A \ B) _ p).trans ((pair_restrictionGraph A (A \ B) _ _).mp hzd).2.2.symm)
    exact ⟨p,(mem_iff_projections A B hBA G p).mpr ⟨hbp.symm ▸ hbj,hdp.symm ▸ hdl⟩,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨label_mem _ p,label _ (project A B hBA p),
      (mem_genericFilterSet _ _ _).mpr ⟨_,projected_contains A B hBA G hp,rfl⟩,
      label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p),
      (mem_genericFilterSet _ _ _).mpr ⟨_,projected_contains A (A \ B) _ G hp,rfl⟩,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,
      (pair_restrictionGraph A (A \ B) _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A _ _ p⟩⟩

end TuringRigidity.CohenFactorReconstruction

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFactorIteration
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFactorIteration
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCohenPartition InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem extension_eq (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    let J := projected A B hBA G
    let L := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
    genericExtensionSet (genericExtensionSet M (conditions B) J.carrier)
      (conditions (A \ B)) L.carrier = genericExtensionSet M (conditions A) G.carrier := by
  let J := projected A B hBA G
  let L := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
  let N := genericExtensionSet M (conditions B) J.carrier
  let V := genericExtensionSet N (conditions (A \ B)) L.carrier
  let O := genericExtensionSet M (conditions A) G.carrier
  have hD := complement_mem M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hcD := conditions_mem M (A \ B) hM hT hD
  have hJG := projected_groundGeneric M A B hM hT hA hB hBA G hG
  have hLG := CohenUntouchedGeneric.untouched_ground_generic M A B hM hT hA hB hBA G hG
  have hGt : ⊤ ∈ G.carrier := by obtain ⟨p,hp⟩ := G.nonempty; exact G.upper le_top hp
  have hJt : ⊤ ∈ J.carrier := by obtain ⟨p,hp⟩ := J.nonempty; exact J.upper le_top hp
  have hLt : ⊤ ∈ L.carrier := by obtain ⟨p,hp⟩ := L.nonempty; exact L.upper le_top hp
  have hN : Transitive N := genericExtensionSet_transitive M _ hM J.carrier
  have hTN : SourceT N := extension_sourceT M hM hT hcB (InternalCollapse.orderSet_mem M hM hT hcB)
    (InternalCollapse.orderSet_pair _) J hJG hJt
  have hMN : M ⊆ N := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB J.carrier hJt
  have hjN := genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB J.carrier hJt
  have hV : Transitive V := genericExtensionSet_transitive N _ hN L.carrier
  have hTV : SourceT V := extension_sourceT N hN hTN (hMN hcD)
    (InternalCollapse.orderSet_mem N hN hTN (hMN hcD)) (InternalCollapse.orderSet_pair _) L hLG hLt
  have hNV : N ⊆ V := ground_inclusion_set N _ hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity (hMN hcD) L.carrier hLt
  have hlV := genericFilterSet_mem_extension N _ hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity (hMN hcD) L.carrier hLt
  have hO : Transitive O := genericExtensionSet_transitive M _ hM G.carrier
  have hTO : SourceT O := extension_sourceT M hM hT hcA (InternalCollapse.orderSet_mem M hM hT hcA)
    (InternalCollapse.orderSet_pair _) G hG hGt
  have hMO : M ⊆ O := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcA G.carrier hGt
  have hgO := genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcA G.carrier hGt
  have hNO : N ⊆ O := InternalColumnExtension.column_extension_subset M A B hM hT hA hB hBA G hG
  have hlO : genericFilterSet (conditions (A \ B)) L.carrier ∈ O := by
    rw [InternalColumnExtension.projected_filter_image]
    exact InternalColumnExtension.filterImage_mem O A (A \ B) _ hO hTO (hMO hA) (hMO hD) hgO
  have hVO : V ⊆ O := InternalNameEvaluation.extension_subset N O hO hTO hNO L.carrier hlO
  have hgV : genericFilterSet (conditions A) G.carrier ∈ V := by
    rw [←CohenFactorReconstruction.reconstruct_filter A B hBA G]
    exact CohenFactorReconstruction.reconstruct_mem V A B _ _ hV hTV
      (hNV (hMN hA)) (hNV (hMN hB)) (hNV hjN) hlV
  have hOV : O ⊆ V := InternalNameEvaluation.extension_subset M V hV hTV
    (fun _ hx => hNV (hMN hx)) G.carrier hgV
  exact ZFSet.ext (fun x => ⟨fun hx => hVO hx,fun hx => hOV hx⟩)

end TuringRigidity.CohenFactorIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductConditions
open TransitiveNameModel BoundedSetTheory
attribute [local instance] InternalCollapse.order

theorem code_mem (M p s : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hp : p ∈ M) (hs : s ∈ M) : code p s ∈ M := by
  have hn (n : ℕ) : natSet n ∈ M :=
    hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact binary_union_mem M hM hT.pairing hT.union
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 0)) hp)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 1)) hs)

theorem codeFormula_spec (p s z z0 z1 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) :
    (codeFormula p s z z0 z1).Eval e ↔ e z = code (e p) (e s) := by
  simp only [codeFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_disj,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,h0,h1]
  constructor
  · rintro ⟨ha,hb,hc⟩
    apply ZFSet.ext; intro x
    exact ⟨fun hx => (mem_code _ _ _).mpr (ha x hx),fun hx =>
      ((mem_code _ _ _).mp hx).elim (fun ⟨y,hy,he⟩ => he ▸ hb y hy)
        (fun ⟨y,hy,he⟩ => he ▸ hc y hy)⟩
  · intro h; rw [h]
    exact ⟨fun x hx => (mem_code _ _ _).mp hx,
      fun x hx => (left_mem _ _ _).mpr hx,fun x hx => (right_mem _ _ _).mpr hx⟩

theorem code_bounded (a b p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
    code p s ⊆ bound a b :=
  (code_subset _ _ _ _).mpr ⟨fun _ hx => ZFSet.mem_sUnion.mpr ⟨p,hp,hx⟩,
    fun _ hx => ZFSet.mem_sUnion.mpr ⟨s,hs,hx⟩⟩

theorem internal_product (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) :
    ∃ c ∈ M, (∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) ∧
      ∃ g ∈ M, FunctionGraph (ZFSet.prod a b) c g ∧
        (∀ p ∈ a, ∀ s ∈ b, ∀ z, ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s) ∧
        (∀ z ∈ c, ∃ x ∈ ZFSet.prod a b, ZFSet.pair x z ∈ g) := by
  have hbound := code_mem M _ _ hM hT (union_mem M hM hT.union ha) (union_mem M hM hT.union hb)
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hbound
  have hcode (p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) : code p s ∈ Q :=
    (hQdef _).mpr ⟨code_mem M p s hM hT (hM a ha p hp) (hM b hb s hs),code_bounded a b p s hp hs⟩
  let e := cons a (cons b (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact ha; exact hb
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  let c := Q.sep (fun z => ∃ p ∈ a, ∃ s ∈ b, z = code p s)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  have hc : c ∈ M := by
    simpa only [c,Formula.Eval,hsepCode,
      cons_zero,cons_succ,e] using
      sep_mem M hM hT.separation.finitePrefix.bounded
        (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hQ
  have hcs (z : ZFSet.{0}) : z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s := by
    change (z ∈ Q.sep _) ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨And.right,fun h@⟨p,hp,s,hs,hz⟩ => ⟨hz ▸ hcode p s hp hs,h⟩⟩
  let v := cons (ZFSet.prod a b) (cons c e)
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb
  have hv : ∀ i, v i ∈ M := by
    intro i; rcases i with _|_|i; exact hprod; exact hc; exact he i
  have hgraphCode (left right value point entry : ZFSet.{0}) :
      (codeFormula 1 0 2 9 10).Eval
        (cons right (cons left (cons value (cons point (cons entry v))))) ↔
          value = code left right :=
    codeFormula_spec 1 0 2 9 10 _ rfl rfl
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.existsMem 7 (.conj (.orderedPair 3 1 0) (codeFormula 1 0 2 9 10))))))
  let g := (ZFSet.prod (ZFSet.prod a b) c).sep (fun z => φ.Eval (cons z v))
  have hg : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hprod hc)
  have hgs (p s z : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
      ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s := by
    simp only [g,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      hgraphCode,cons_zero,cons_succ,v,e]
    constructor
    · rintro ⟨_,x,_,y,_,hxy,p',_,s',_,hx,hy⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hx
      exact hy
    · intro hz
      have hzc := (hcs z).mpr ⟨p,hp,s,hs,hz⟩
      have hps := ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hps,hzc⟩,_,hps,z,hzc,rfl,p,hp,s,hs,rfl,hz⟩
  refine ⟨c,hc,hcs,g,hg,⟨?_,?_⟩,(fun p hp s hs z => hgs p s z hp hs),?_⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨p,hp,s,hs,rfl⟩ := ZFSet.mem_prod.mp hx
    exact ⟨code p s,(hcs _).mpr ⟨p,hp,s,hs,rfl⟩,(hgs p s _ hp hs).mpr rfl,
      fun y _ hy => (hgs p s y hp hs).mp hy⟩
  · intro z hz
    obtain ⟨p,hp,s,hs,hz⟩ := (hcs z).mp hz
    exact ⟨ZFSet.pair p s,ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩,(hgs p s z hp hs).mpr hz⟩

end TuringRigidity.TaggedProductConditions

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem joint_mem (a b c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))
    (p : Conditions a) (s : Conditions b) :
    productMap a b c hcs (p,s) ∈ (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  change (productIso a b c hcs).symm ((productIso a b c hcs) (p,s)) ∈ (SourceEquationTail.productFilter G H).carrier ↔ _
  rw [OrderIso.symm_apply_apply]
  rfl

theorem sectionSet_mem (M a b D r : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) (hr : r ∈ M) : sectionSet a b D r ∈ M := by
  let e := cons b (cons D (cons r (cons (natSet 0) (fun _ => natSet 1))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hb; exact hD; exact hr
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsectionCode (left right value : ZFSet.{0}) :
      (codeFormula 2 1 0 6 7).Eval (cons value (cons right (cons left e))) ↔
        value = code left right :=
    codeFormula_spec 2 1 0 6 7 _ rfl rfl
  simpa only [sectionSet,Formula.Eval,hsectionCode,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (codeFormula 2 1 0 6 7) (.subset 5 1)))) e he ha

theorem fiberSet_mem (N b D g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hD : D ∈ N) (hg : g ∈ N) : fiberSet b D g ∈ N := by
  let e := cons g (cons D (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i
    exact hg; exact hD
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hfiberCode (left right value : ZFSet.{0}) :
      (codeFormula 1 2 0 5 6).Eval (cons value (cons left (cons right e))) ↔
        value = code left right :=
    codeFormula_spec 1 2 0 5 6 _ rfl rfl
  simpa only [fiberSet,Formula.Eval,hfiberCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 2 0 5 6))) e he hb

theorem sectionSet_dense (a b c D : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hD : Dense {x : Conditions c | label c x ∈ D}) (r : Conditions b) :
    Dense {p : Conditions a | label a p ∈ sectionSet a b D (label b r)} := by
  intro p
  obtain ⟨x,hx,hxD⟩ := hD (productMap a b c hcs (p,r))
  let y := (productIso a b c hcs).symm x
  have hy : y ≤ (p,r) := by
    have hh := (productIso a b c hcs).symm.monotone hx
    change (productIso a b c hcs).symm x ≤ (productIso a b c hcs).symm ((productIso a b c hcs) (p,r)) at hh
    simpa only [OrderIso.symm_apply_apply] using hh
  have hl : label c x = code (label a y.1) (label b y.2) := by
    rw [←label_productMap a b c hcs y]
    exact congrArg (label c) ((productIso a b c hcs).apply_symm_apply x).symm
  exact ⟨y.1,hy.1,ZFSet.mem_sep.mpr ⟨label_mem a y.1,label b y.2,label_mem b y.2,
    label c x,hxD,hl,hy.2⟩⟩

theorem fiberSet_dense (M a b c D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hd : Dense {x : Conditions c | label c x ∈ D})
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    Dense {r : Conditions b | label b r ∈ fiberSet b D (genericFilterSet a G.carrier)} := by
  intro r
  obtain ⟨p,hp,hpr⟩ := hG (sectionSet a b D (label b r))
    (sectionSet_mem M a b D _ hM hT ha hb hD (hM b hb _ (label_mem b r)))
    (sectionSet_dense a b c D hcs hd r)
  obtain ⟨_,s,hs,z,hz,hzs,hrs⟩ := ZFSet.mem_sep.mp hpr
  obtain ⟨s,rfl⟩ := label_surjective b hs
  exact ⟨s,hrs,ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,
    (mem_genericFilterSet a G.carrier _).mpr ⟨p,hp,rfl⟩,z,hz,hzs⟩⟩

theorem joint_ground_generic (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    AtomicForcing.GroundGeneric M (joint a b c hcs G H) := by
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  intro D hD hd
  obtain ⟨s,hs,hsE⟩ := hH (fiberSet b D (genericFilterSet a G.carrier))
    (fiberSet_mem _ b D _ hN hTN (hMN hb) (hMN hD) hgN)
    (fiberSet_dense M a b c D hM hT ha hb hD hcs hd G hG)
  obtain ⟨_,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hsE
  obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
  refine ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr ⟨hpG,hs⟩,?_⟩
  rw [label_productMap,←he]
  exact hz

end TuringRigidity.TaggedProductGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductRecovery
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductRecovery
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting TaggedProductGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem jointSet_mem (N c g h : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hg : g ∈ N) (hh : h ∈ N) : jointSet c g h ∈ N := by
  let e := cons g (cons h (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i; exact hg; exact hh
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  simpa only [jointSet,Formula.Eval,hsepCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hc

variable (a b c : ZFSet.{0})
variable (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
variable (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))

theorem code_mem_joint (p : Conditions a) (s : Conditions b) :
    code (label a p) (label b s) ∈ genericFilterSet c (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  rw [mem_genericFilterSet]
  constructor
  · rintro ⟨r,hr,he⟩
    have hrps : r = productMap a b c hcs (p,s) := label_injective c
      (he.trans (label_productMap a b c hcs (p,s)).symm)
    exact (joint_mem a b c hcs G H p s).mp (hrps ▸ hr)
  · intro h
    exact ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr h,
      label_productMap a b c hcs (p,s)⟩

theorem jointFilterSet_eq :
    genericFilterSet c (joint a b c hcs G H).carrier =
      jointSet c (genericFilterSet a G.carrier) (genericFilterSet b H.carrier) := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨r,_,hrz⟩ := (mem_genericFilterSet c _ z).mp hz
    have hzc := hrz ▸ label_mem c r
    obtain ⟨p,hp,s,hs,he⟩ := (hcs z).mp hzc
    obtain ⟨p,rfl⟩ := label_surjective a hp
    obtain ⟨s,rfl⟩ := label_surjective b hs
    obtain ⟨hpG,hsH⟩ := (code_mem_joint a b c hcs G H p s).mp (he ▸ hz)
    exact ZFSet.mem_sep.mpr ⟨hzc,label a p,(mem_genericFilterSet a _ _).mpr ⟨p,hpG,rfl⟩,
      label b s,(mem_genericFilterSet b _ _).mpr ⟨s,hsH,rfl⟩,he⟩
  · intro hz
    obtain ⟨_,p,hp,s,hs,he⟩ := ZFSet.mem_sep.mp hz
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
    obtain ⟨s,hsH,rfl⟩ := (mem_genericFilterSet b H.carrier s).mp hs
    exact he.symm ▸ (code_mem_joint a b c hcs G H p s).mpr ⟨hpG,hsH⟩

theorem leftFilterSet_eq : genericFilterSet a G.carrier =
    sectionSet a b (genericFilterSet c (joint a b c hcs G H).carrier) ∅ := by
  apply ZFSet.ext; intro p
  constructor
  · intro hp
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a _ p).mp hp
    obtain ⟨s,hs⟩ := H.nonempty
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b s,label_mem b s,
      code (label a p) (label b s),(code_mem_joint a b c hcs G H p s).mpr ⟨hpG,hs⟩,rfl,
      fun x hx => False.elim (ZFSet.notMem_empty x hx)⟩
  · intro hp
    obtain ⟨hpa,s,hs,z,hz,he,_⟩ := ZFSet.mem_sep.mp hp
    obtain ⟨p,rfl⟩ := label_surjective a hpa
    obtain ⟨s,rfl⟩ := label_surjective b hs
    have hpG := ((code_mem_joint a b c hcs G H p s).mp (he ▸ hz)).1
    exact (mem_genericFilterSet a _ _).mpr ⟨p,hpG,rfl⟩

theorem rightFilterSet_eq : genericFilterSet b H.carrier =
    fiberSet b (genericFilterSet c (joint a b c hcs G H).carrier) a := by
  apply ZFSet.ext; intro s
  constructor
  · intro hs
    obtain ⟨s,hsH,rfl⟩ := (mem_genericFilterSet b _ s).mp hs
    obtain ⟨p,hp⟩ := G.nonempty
    exact ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,label_mem a p,
      code (label a p) (label b s),(code_mem_joint a b c hcs G H p s).mpr ⟨hp,hsH⟩,rfl⟩
  · intro hs
    obtain ⟨hsb,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hs
    obtain ⟨p,rfl⟩ := label_surjective a hp
    obtain ⟨s,rfl⟩ := label_surjective b hsb
    have hsH := ((code_mem_joint a b c hcs G H p s).mp (he ▸ hz)).2
    exact (mem_genericFilterSet b _ _).mpr ⟨s,hsH,rfl⟩

end TuringRigidity.TaggedProductRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductExtension
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open TaggedProductGeneric TaggedProductRecovery RegularTreeExtension
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_eq (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    genericExtensionSet M c (joint a b c hcs G H).carrier =
      genericExtensionSet (genericExtensionSet M a G.carrier) b H.carrier := by
  let N := genericExtensionSet M a G.carrier
  let V := genericExtensionSet N b H.carrier
  let J := joint a b c hcs G H
  let O := genericExtensionSet M c J.carrier
  obtain ⟨hN,hTN,hMN,hgN⟩ := extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hNV,hhV⟩ := extension_properties N b hN hTN (hMN hb) H hH
  have hJ := joint_ground_generic M a b c hM hT ha hb hcs G hG H hH
  obtain ⟨hO,hTO,hMO,hjO⟩ := extension_properties M c hM hT hc J hJ
  have hgO : genericFilterSet a G.carrier ∈ O := by
    rw [leftFilterSet_eq a b c hcs G H]
    exact sectionSet_mem O a b _ ∅ hO hTO (hMO ha) (hMO hb) hjO
      (hO _ (sourceT_omega_mem O hO hTO) _ ZFSet.omega_zero)
  have hhO : genericFilterSet b H.carrier ∈ O := by
    rw [rightFilterSet_eq a b c hcs G H]
    exact fiberSet_mem O b _ a hO hTO (hMO hb) hjO (hMO ha)
  have hNO : N ⊆ O := InternalNameEvaluation.extension_subset M O hO hTO hMO G.carrier hgO
  have hVO : V ⊆ O := InternalNameEvaluation.extension_subset N O hO hTO hNO H.carrier hhO
  have hjV : genericFilterSet c J.carrier ∈ V := by
    rw [jointFilterSet_eq a b c hcs G H]
    exact jointSet_mem V c _ _ hV hTV (hNV (hMN hc)) (hNV hgN) hhV
  have hOV : O ⊆ V := InternalNameEvaluation.extension_subset M V hV hTV
    (fun _ hx => hNV (hMN hx)) J.carrier hjV
  exact ZFSet.ext (fun x => ⟨fun hx => hOV hx,fun hx => hVO hx⟩)

end TuringRigidity.TaggedProductExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenIteratedAbsorption
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenIteratedAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem same_generics_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) H) :
    ∃ W : GenericFilter (Conditions InternalCohen.conditions),
      AtomicForcing.GroundGeneric M W ∧
        genericExtensionSet M InternalCohen.conditions W.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier)
            (CohenGroundPoset.conditions ZFSet.omega) H.carrier := by
  obtain ⟨c,hc,hcs,habs⟩ := CohenAbsorptionGeneric.product_generic_absorption M q hM hT hq hct
  have hb := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  let J := TaggedProductGeneric.joint q (CohenGroundPoset.conditions ZFSet.omega) c hcs G H
  have hJ := TaggedProductGeneric.joint_ground_generic M q _ c hM hT hq hb hcs G hG H hH
  obtain ⟨W,hW,hWe⟩ := habs J hJ
  exact ⟨W,hW,hWe.trans (TaggedProductExtension.extension_eq M q _ c hM hT hq hb hc hcs G hG H hH)⟩

end TuringRigidity.CohenIteratedAbsorption

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalDenseInclusion
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalDenseInclusion
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem embed_mem_push (a b : ZFSet.{0}) (hab : a ⊆ b)
    (G : GenericFilter (Conditions a)) (p : Conditions a) :
    embed a b hab p ∈ (push a b hab G).carrier ↔ p ∈ G.carrier := by
  constructor
  · rintro ⟨q,hq,hqp⟩; exact G.upper ((embed_le_iff a b hab q p).mp hqp) hq
  · intro hp; exact ⟨p,hp,le_rfl⟩

theorem densePull_mem (M a b D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) : densePull a b D ∈ M := by
  let e := cons b (fun _ => D)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hb; exact hD
  simpa only [densePull,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.member 0 3) (.subset 0 1))) e he ha

theorem push_ground_generic (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hab : a ⊆ b)
    (hd : ∀ q ∈ b, ∃ p ∈ a, q ⊆ p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (push a b hab G) := by
  intro D hD hden
  have hpull : Dense {p : Conditions a | label a p ∈ densePull a b D} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hden (embed a b hab p)
    obtain ⟨r,hr,hqr⟩ := hd (label b q) (label_mem b q)
    obtain ⟨r,rfl⟩ := label_surjective a hr
    have hpr : label a p ⊆ label a r :=
      fun z hz => hqr (hqp ((label_embed a b hab p).symm ▸ hz))
    exact ⟨r,hpr,ZFSet.mem_sep.mpr ⟨label_mem a r,label b q,label_mem b q,hqD,hqr⟩⟩
  obtain ⟨p,hp,hpD⟩ := hG (densePull a b D) (densePull_mem M a b D hM hT ha hb hD) hpull
  obtain ⟨_,q,hqb,hqD,hqp⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨q,rfl⟩ := label_surjective b hqb
  exact ⟨q,⟨p,hp,by change label b q ⊆ label b (embed a b hab p); rwa [label_embed]⟩,hqD⟩

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

theorem dense_inclusion : ∀ q ∈ CohenGroundPoset.conditions ZFSet.omega,
    ∃ p ∈ InternalCohen.conditions, q ⊆ p := by
  intro q hq
  obtain ⟨s,hs⟩ := condition_extends_prefix q hq
  exact ⟨wordCode s,(mem_conditions _).mpr ⟨s.length,wordCode_function s⟩,hs⟩

end TuringRigidity.CohenPrefixDensity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DenseInclusionExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.DenseInclusionExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem upperSet_mem (N b g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hg : g ∈ N) : upperSet b g ∈ N := by
  let e := fun _ : ℕ => g
  simpa only [upperSet,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.subset 1 0)) e (fun _ => hg) hb

theorem restrictSet_mem (N a k : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (ha : a ∈ N) (hk : k ∈ N) : restrictSet a k ∈ N := by
  let e := fun _ : ℕ => k
  simpa only [restrictSet,Formula.Eval,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded (.member 0 1) e (fun _ => hk) ha

theorem pushFilterSet_eq (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    genericFilterSet b (push a b hab G).carrier = upperSet b (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨q,⟨p,hp,hpq⟩,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    refine ZFSet.mem_sep.mpr ⟨label_mem b q,label a p,
      (mem_genericFilterSet _ _ _).mpr ⟨p,hp,rfl⟩,?_⟩
    change label b q ⊆ label b (embed a b hab p) at hpq
    rwa [label_embed] at hpq
  · intro hx
    obtain ⟨hxb,p,hpg,hxp⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨q,rfl⟩ := label_surjective b hxb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ p).mp hpg
    exact (mem_genericFilterSet _ _ _).mpr ⟨q,⟨p,hp,by
      change label b q ⊆ label b (embed a b hab p); rwa [label_embed]⟩,rfl⟩

theorem originalFilterSet_eq (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier = restrictSet a (genericFilterSet b (push a b hab G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,(mem_genericFilterSet _ _ _).mpr
      ⟨embed a b hab p,(embed_mem_push a b hab G p).mpr hp,label_embed a b hab p⟩⟩
  · intro hx
    obtain ⟨hxa,hxk⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,hqe⟩ := (mem_genericFilterSet _ _ _).mp hxk
    have he : q = embed a b hab p := label_injective b (hqe.trans (label_embed a b hab p).symm)
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,(embed_mem_push a b hab G p).mp (he ▸ hq),rfl⟩

theorem extension_eq (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hab : a ⊆ b)
    (hd : ∀ q ∈ b, ∃ p ∈ a, q ⊆ p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (push a b hab G).carrier = genericExtensionSet M a G.carrier := by
  let K := push a b hab G
  have hK := push_ground_generic M a b hM hT ha hb hab hd G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [pushFilterSet_eq]
    exact upperSet_mem _ b _ hN hTN (hMN hb) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b hab G]
    exact restrictSet_mem _ a _ hV hTV (hMV ha) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.DenseInclusionExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenLiteralAbsorption
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenLiteralAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion CohenPrefixDensity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prefix_transport (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (W : GenericFilter (Conditions InternalCohen.conditions)) (hW : AtomicForcing.GroundGeneric M W) :
    let K := push InternalCohen.conditions (CohenGroundPoset.conditions ZFSet.omega) conditions_subset W
    AtomicForcing.GroundGeneric M K ∧
      genericExtensionSet M (CohenGroundPoset.conditions ZFSet.omega) K.carrier =
        genericExtensionSet M InternalCohen.conditions W.carrier := by
  have ha := InternalCohen.conditions_mem M hM hT
  have hb := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  exact ⟨push_ground_generic M _ _ hM hT ha hb conditions_subset dense_inclusion W hW,
    DenseInclusionExtension.extension_eq M _ _ hM hT ha hb conditions_subset dense_inclusion W hW⟩

theorem same_generics_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) H) :
    ∃ K : GenericFilter (Conditions (CohenGroundPoset.conditions ZFSet.omega)),
      AtomicForcing.GroundGeneric M K ∧
        genericExtensionSet M (CohenGroundPoset.conditions ZFSet.omega) K.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier)
            (CohenGroundPoset.conditions ZFSet.omega) H.carrier := by
  obtain ⟨W,hW,hWe⟩ := CohenIteratedAbsorption.same_generics_absorption M q hM hT hq hct G hG H hH
  obtain ⟨hK,hKe⟩ := prefix_transport M hM hT W hW
  exact ⟨_,hK,hKe.trans hWe⟩

end TuringRigidity.CohenLiteralAbsorption

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

theorem imageSet_mem (M b f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hb : b ∈ M) (hf : f ∈ M) (hg : g ∈ M) : imageSet b f g ∈ M := by
  let e := cons g (fun _ => f)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hg; exact hf
  simpa only [imageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3)) e he hb

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

theorem mapFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet b (AutomorphismName.mapFilter e G).carrier =
      imageSet b f (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro y
  constructor
  · intro hy
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    exact ZFSet.mem_sep.mpr ⟨label_mem b q,label a (e.symm q),
      (mem_genericFilterSet _ _ _).mpr ⟨e.symm q,hq,rfl⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  · intro hy
    obtain ⟨hyb,x,hx,hxy⟩ := ZFSet.mem_sep.mp hy
    obtain ⟨q,rfl⟩ := label_surjective b hyb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩

theorem originalFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier =
      preimageSet a f (genericFilterSet b (AutomorphismName.mapFilter e G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b (e p),
      (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩,
      (he p (e p)).mpr rfl⟩
  · intro hx
    obtain ⟨hxa,y,hy,hxy⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,by simpa [AutomorphismName.mapFilter] using hq,rfl⟩

theorem extension_eq (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (AutomorphismName.mapFilter e G).carrier = genericExtensionSet M a G.carrier := by
  let K := AutomorphismName.mapFilter e G
  have hK := map_ground_generic M a b f hM hT ha hb hf e he G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [mapFilterSet_eq a b f e he G]
    exact imageSet_mem _ b f _ hN hTN (hMN hb) (hMN hf) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b f e he G]
    exact preimageSet_mem _ a f _ hV hTV (hMV ha) (hMV hf) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.InternalOrderIsoTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInverseGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalInverseGraph
open TransitiveNameModel BoundedSetTheory

theorem pair_inverse (A B f y x : ZFSet.{0}) :
    ZFSet.pair y x ∈ inverse A B f ↔ y ∈ B ∧ x ∈ A ∧ ZFSet.pair x y ∈ f := by
  simp only [inverse,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y',hy,x',hx,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hy,hx,h⟩
  · rintro ⟨hy,hx,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hy,hx⟩,y,hy,x,hx,rfl,h⟩

theorem inverse_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : inverse A B f ∈ M := by
  let e := cons B (cons A (fun _ => f))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hB; exact hA; exact hf
  simpa only [inverse,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.pairMem 0 1 5)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hB hA)

end TuringRigidity.InternalInverseGraph

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
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
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

theorem internal_column_iso (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (ha : a ∈ M) :
    ∃ e : Conditions (conditions (ZFSet.prod {a} ZFSet.omega)) ≃o
        Conditions (conditions ZFSet.omega),
      ∃ f ∈ M, ∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p := by
  have hW := sourceT_omega_mem M hM hT
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hW
  obtain ⟨e,hf,hfe,_⟩ := InternalCohenReindex.internal_reindex M _ _ (graph a ZFSet.omega)
    hM hT hA hW (graph_mem M a _ hM hT ha hW) (graph_function a _)
    (graph_injective a _) (graph_onto a _)
  exact ⟨e,_,hf,hfe⟩

end TuringRigidity.InternalSingletonColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnAbsorption
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem absorb_column (M q A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) (hA : A ∈ M) (ha : a ∈ M)
    (hBA : ZFSet.prod {a} ZFSet.omega ⊆ A)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (L : GenericFilter (Conditions (conditions A)))
    (hL : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) L) :
    let B := ZFSet.prod {a} ZFSet.omega
    let R := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) L
    ∃ W : GenericFilter (Conditions (conditions ZFSet.omega)),
      AtomicForcing.GroundGeneric M W ∧
      AtomicForcing.GroundGeneric (genericExtensionSet M (conditions ZFSet.omega) W.carrier) R ∧
      genericExtensionSet (genericExtensionSet M (conditions ZFSet.omega) W.carrier)
        (conditions (A \ B)) R.carrier =
          genericExtensionSet (genericExtensionSet M q G.carrier) (conditions A) L.carrier := by
  let N := genericExtensionSet M q G.carrier
  let B := ZFSet.prod {a} ZFSet.omega
  let J := projected A B hBA L
  let R := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) L
  obtain ⟨hN,hTN,hMN,_⟩ := RegularTreeExtension.extension_properties M q hM hT hq G hG
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hω
  have hcB := conditions_mem M B hM hT hB
  have hcω := conditions_mem M ZFSet.omega hM hT hω
  have hJ := projected_groundGeneric N A B hN hTN (hMN hA) (hMN hB) hBA L hL
  have hR := CohenUntouchedGeneric.untouched_ground_generic N A B hN hTN (hMN hA) (hMN hB) hBA L hL
  have hLR := CohenFactorIteration.extension_eq N A B hN hTN (hMN hA) (hMN hB) hBA L hL
  obtain ⟨e,f,hf,hfe⟩ := InternalSingletonColumn.internal_column_iso M a hM hT ha
  let H := AutomorphismName.mapFilter e J
  have hH := InternalOrderIsoTransport.map_ground_generic N _ _ f hN hTN
    (hMN hcB) (hMN hcω) (hMN hf) e hfe J hJ
  have hHe := InternalOrderIsoTransport.extension_eq N _ _ f hN hTN
    (hMN hcB) (hMN hcω) (hMN hf) e hfe J hJ
  obtain ⟨W,hW,hWe⟩ := CohenLiteralAbsorption.same_generics_absorption M q hM hT hq hct G hG H hH
  have he : genericExtensionSet M (conditions ZFSet.omega) W.carrier =
      genericExtensionSet N (conditions B) J.carrier := hWe.trans hHe
  refine ⟨W,hW,?_,?_⟩
  · rw [he]; exact hR
  · rw [he]; exact hLR

end TuringRigidity.CohenColumnAbsorption

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPartitionBridge
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPartitionBridge
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenFactor
open TaggedProductConditions CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem pair_bridge (a b T f g x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ bridge a b T f g ↔
      x ∈ a ∧ y ∈ b ∧ ∃ t ∈ T, ZFSet.pair t x ∈ f ∧ ZFSet.pair y t ∈ g := by
  constructor
  · intro h
    obtain ⟨_,x',hx,y',hy,he,ht⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,ht⟩
  · rintro ⟨hx,hy,ht⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,ht⟩

theorem bridge_mem (M a b T f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hTm : T ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    bridge a b T f g ∈ M := by
  let e := cons a (cons b (cons T (cons f (fun _ => g))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i; exact ha; exact hb; exact hTm; exact hf; exact hg
  simpa only [bridge,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.conj (.pairMem 0 2 7) (.pairMem 1 0 8)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)

theorem internal_union_iso (M A B c f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A) (hc : c ∈ M) (hf : f ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions B, ∃ s ∈ conditions (A \ B), z = code p s)
    (hfs : ∀ p ∈ conditions B, ∀ s ∈ conditions (A \ B), ∀ z,
      ZFSet.pair (ZFSet.pair p s) z ∈ f ↔ z = code p s) :
    let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
    ∃ g ∈ M, ∀ p q, ZFSet.pair (label c p) (label (conditions A) q) ∈ g ↔ q = e p := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hfac.1 hfac.2.1
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
  refine ⟨bridge c (conditions A) (productCode A B) f (factorGraph A B),
    bridge_mem M _ _ _ _ _ hM hT hc hcA hprod hf hfac.2.2.2.2,?_⟩
  intro p q
  obtain ⟨⟨r,s⟩,rfl⟩ := (productIso (conditions B) (conditions (A \ B)) c hcs).surjective p
  have heval : e (productIso (conditions B) (conditions (A \ B)) c hcs (r,s)) =
      (factorIso A B hBA).symm (r,s) := by
    change (factorIso A B hBA).symm
      ((productIso (conditions B) (conditions (A \ B)) c hcs).symm
        ((productIso (conditions B) (conditions (A \ B)) c hcs) (r,s))) = _
    rw [OrderIso.symm_apply_apply]
  rw [pair_bridge]
  simp only [label_mem,true_and]
  change (∃ t ∈ productCode A B,
    ZFSet.pair t (label c (productMap _ _ c hcs (r,s))) ∈ f ∧
      ZFSet.pair (label _ q) t ∈ factorGraph A B) ↔ q = e ((productIso _ _ c hcs) (r,s))
  rw [label_productMap,heval]
  constructor
  · rintro ⟨t,ht,htf,htg⟩
    obtain ⟨u,hu,v,hv,rfl⟩ := ZFSet.mem_prod.mp ht
    obtain ⟨u,rfl⟩ := label_surjective (conditions B) hu
    obtain ⟨v,rfl⟩ := label_surjective (conditions (A \ B)) hv
    obtain ⟨hu,hv⟩ := (code_injective _ _ _ _).mp ((hfs _ (label_mem _ u) _ (label_mem _ v) _).mp htf)
    have hur : u = r := label_injective _ hu.symm
    have hvs : v = s := label_injective _ hv.symm
    subst u; subst v
    have hq := (factorGraph_is_iso_graph A B hBA q r s).mp htg
    simpa only [OrderIso.symm_apply_apply] using congrArg (factorIso A B hBA).symm hq
  · intro hq
    refine ⟨ZFSet.pair (label _ r) (label _ s),ZFSet.pair_mem_prod.mpr ⟨label_mem _ r,label_mem _ s⟩,
      (hfs _ (label_mem _ r) _ (label_mem _ s) _).mpr rfl,?_⟩
    apply (factorGraph_is_iso_graph A B hBA q r s).mpr
    rw [hq,OrderIso.apply_symm_apply]

end TuringRigidity.CohenPartitionBridge

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPartitionJoint
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPartitionJoint
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open TaggedProductConditions CohenProductSplitting InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem reassemble (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (J : GenericFilter (Conditions (conditions B))) (hJ : AtomicForcing.GroundGeneric M J)
    (R : GenericFilter (Conditions (conditions (A \ B))))
    (hR : AtomicForcing.GroundGeneric (genericExtensionSet M (conditions B) J.carrier) R) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M (conditions B) J.carrier)
          (conditions (A \ B)) R.carrier := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  obtain ⟨c,hc,hcs,f,hf,_,hfs,_⟩ := internal_product M _ _ hM hT hfac.1 hfac.2.1
  let T := TaggedProductGeneric.joint _ _ c hcs J R
  have hTg := TaggedProductGeneric.joint_ground_generic M _ _ c hM hT hfac.1 hfac.2.1 hcs J hJ R hR
  have hTe := TaggedProductExtension.extension_eq M _ _ c hM hT hfac.1 hfac.2.1 hc hcs J hJ R hR
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
  obtain ⟨g,hg,hge⟩ := CohenPartitionBridge.internal_union_iso M A B c f hM hT hA hB hBA hc hf hcs hfs
  refine ⟨AutomorphismName.mapFilter e T,
    InternalOrderIsoTransport.map_ground_generic M _ _ g hM hT hc hcA hg e hge T hTg,?_⟩
  exact (InternalOrderIsoTransport.extension_eq M _ _ g hM hT hc hcA hg e hge T hTg).trans hTe

end TuringRigidity.CohenPartitionJoint

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInverseIso
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalInverseIso
open TransitiveNameModel BoundedSetTheory CountableForcing InternalInverseGraph
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem inverse_graph (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p) :
    inverse a b f ∈ M ∧ ∀ p q,
      ZFSet.pair (label b p) (label a q) ∈ inverse a b f ↔ q = e.symm p := by
  refine ⟨inverse_mem M a b f hM hT ha hb hf,?_⟩
  intro p q
  rw [pair_inverse]
  simp only [label_mem,true_and,he]
  constructor
  · intro h
    apply e.injective
    rw [OrderIso.apply_symm_apply]
    exact h.symm
  · intro h
    rw [h,OrderIso.apply_symm_apply]

end TuringRigidity.InternalInverseIso

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenManyAbsorption
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenManyAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem same_generics_absorption_oai (M q A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) (hA : A ∈ M) (ha : a ∈ M)
    (hBA : ZFSet.prod {a} ZFSet.omega ⊆ A)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (L : GenericFilter (Conditions (conditions A)))
    (hL : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) L) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M q G.carrier) (conditions A) L.carrier := by
  let B := ZFSet.prod {a} ZFSet.omega
  let R := projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) L
  obtain ⟨W,hW,hR,hWR⟩ := CohenColumnAbsorption.absorb_column M q A a hM hT hq hct hA ha hBA G hG L hL
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hω
  have hcB := conditions_mem M B hM hT hB
  have hcω := conditions_mem M ZFSet.omega hM hT hω
  obtain ⟨e,f,hf,hfe⟩ := InternalSingletonColumn.internal_column_iso M a hM hT ha
  obtain ⟨hfi,hfie⟩ := InternalInverseIso.inverse_graph M _ _ f hM hT hcB hcω hf e hfe
  let J := AutomorphismName.mapFilter e.symm W
  have hJ := InternalOrderIsoTransport.map_ground_generic M _ _ _ hM hT hcω hcB hfi e.symm hfie W hW
  have hJe := InternalOrderIsoTransport.extension_eq M _ _ _ hM hT hcω hcB hfi e.symm hfie W hW
  have hRJ : AtomicForcing.GroundGeneric (genericExtensionSet M (conditions B) J.carrier) R := by
    rw [hJe]; exact hR
  obtain ⟨U,hU,hUe⟩ := CohenPartitionJoint.reassemble M A B hM hT hA hB hBA J hJ R hRJ
  refine ⟨U,hU,hUe.trans ?_⟩
  rw [hJe]
  exact hWR

end TuringRigidity.CohenManyAbsorption

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption_oai := @OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption_oai
