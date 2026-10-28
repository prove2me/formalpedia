-- Prove2me | solution 1 for OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:07:52.835396+00:00
-- url     : https://prove2.me/submissions/ecb0186c-c3ff-4508-9247-b970301a8697

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_OriginalRealQuotientModel_original_name_quotient

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteEnumeration
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets RelativeConstructible

theorem rangeFormula_ranges (ω U E g : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (rangeFormula ω U E g).Eval e ↔ Ranges (e U) (e E) (e g) := by
  simp only [rangeFormula,Ranges,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hω]

theorem candidateFormula_spec (ω U C E a : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (candidateFormula ω U C E a).Eval e ↔ e a = candidates (e U) (e C) (e E) := by
  simp only [candidateFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,cons_zero,cons_succ]
  have hr (g : ZFSet.{0}) := rangeFormula_ranges (ω+1) (U+1) (E+1) 0 (cons g e) hω
  simp only [cons_zero,cons_succ] at hr
  simp only [hr]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro g
    exact ⟨fun hg => ZFSet.mem_sep.mpr ⟨hsub hg,(h g (hsub hg)).mp hg⟩,
      fun hg => (h g (ZFSet.mem_sep.mp hg).1).mpr (ZFSet.mem_sep.mp hg).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hg => (ZFSet.mem_sep.mp hg).1,
      fun g hg => ZFSet.mem_sep.trans (and_iff_right hg)⟩

theorem candidates_mem (M U C E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hC : C ∈ M) (hE : E ∈ M) : candidates U C E ∈ M := by
  let e := cons ZFSet.omega (cons U (fun _ => E))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact sourceT_omega_mem M hM hT
    exact hU; exact hE
  have hr (g : ZFSet.{0}) := rangeFormula_ranges 1 2 3 0 (cons g e) rfl
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded (rangeFormula 1 2 3 0) e he hC
  simpa only [hr,candidates,cons_zero,cons_succ,e] using hs

theorem internal_enumeration_selector (M U : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hU : U ∈ M) :
    ∃ C ∈ M, (∀ g, g ∈ C ↔ InternalCollapse.Prefix U g) ∧
      ∃ T ∈ M, FunctionGraph (finiteSubsets U) C T ∧
        ∀ E ∈ finiteSubsets U, ∀ g, ZFSet.pair E g ∈ T → Ranges U E g := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨C,hC,hCdef⟩ := InternalCollapse.conditions_exist_absolute_without_choice M hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hU
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet
    hT.separation.finitePrefix.bounded hT.choice hC
  have hcan (E : ZFSet.{0}) (hE : E ∈ finiteSubsets U) : candidates U C E ∈ q := by
    apply (hqdef _).mpr
    refine ⟨candidates_mem M U C E hM hT hU hC (finite_subset_mem M U E hM hT hU hE),
      fun _ hg => (ZFSet.mem_sep.mp hg).1,?_⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_finiteSubsets U E).mp hE
    refine ⟨tupleGraph v,ZFSet.mem_sep.mpr ⟨(hCdef _).mpr ⟨n,tupleGraph_function U v hv⟩,?_⟩⟩
    exact (rangeFormula_ranges 0 1 2 3
      (cons ZFSet.omega (cons U (cons (ZFSet.range v) (fun _ => tupleGraph v)))) rfl).mp
      ((rangeFormula_spec 0 1 2 3 _ rfl hv rfl).mpr rfl)
  let S := finiteSubsets U
  let e := cons ZFSet.omega (cons U (cons C (cons S (cons q (fun _ => s)))))
  let φ : Formula := .existsMem 4 (.existsMem 4 (.conj (.orderedPair 2 1 0)
    (.existsMem 7 (.conj (candidateFormula 4 5 6 2 0) (.pairMem 0 1 9)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hω; exact hU; exact hC; exact finiteSubsets_mem M U hM hT hU
    exact hq; exact hsM
  let T := (ZFSet.prod S C).sep (fun z => φ.Eval (cons z e))
  have hTM : T ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (finiteSubsets_mem M U hM hT hU) hC)
  have hmem (z : ZFSet.{0}) : z ∈ T ↔ ∃ E ∈ S, ∃ g ∈ C,
      z = ZFSet.pair E g ∧ ZFSet.pair (candidates U C E) g ∈ s := by
    simp only [T,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,E,hE,g,hg,hz,a,_,ha,hag⟩
      have ha' := (candidateFormula_spec 4 5 6 2 0 _ rfl).mp ha
      change a = candidates U C E at ha'
      exact ⟨E,hE,g,hg,hz,ha' ▸ hag⟩
    · rintro ⟨E,hE,g,hg,rfl,hag⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨E,hE,g,hg,rfl⟩,E,hE,g,hg,rfl,
        candidates U C E,hcan E hE,(candidateFormula_spec 4 5 6 2 0 _ rfl).mpr rfl,hag⟩
  refine ⟨C,hC,hCdef,T,hTM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨E,hE,g,hg,hz,_⟩ := (hmem z).mp hz
    exact ⟨E,hE,g,hg,hz⟩
  · intro E hE
    obtain ⟨g,hg,hag,_⟩ := hs.2 _ (hcan E hE)
    have hgC := (ZFSet.mem_sep.mp hg).1
    refine ⟨g,hgC,(hmem _).mpr ⟨E,hE,g,hgC,rfl,hag⟩,?_⟩
    intro g' _ hEg'
    obtain ⟨E',_,g'',_,hp,hag'⟩ := (hmem _).mp hEg'
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hs.functional hag' hag
  · intro E _ g hEg
    obtain ⟨E',_,g',_,hp,hag⟩ := (hmem _).mp hEg
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact (ZFSet.mem_sep.mp (InternalWellOrder.choice_value_mem hs hag)).2

end TuringRigidity.InternalFiniteEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableFiniteUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableFiniteUnion
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteEnumeration

theorem entryFormula_spec (U g d k x : ℕ) (e : ℕ → ZFSet.{0}) :
    (entryFormula U g d k x).Eval e ↔ Entry (e U) (e g) (e d) (e k) (e x) := by
  simp only [entryFormula,Entry,Formula.eval_disj,Formula.eval_allMem,
    Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]

theorem entry_exists_unique (U g d k : ZFSet.{0}) (hg : InternalCollapse.Prefix U g)
    (hd : d ∈ U) : ∃ x ∈ U, Entry U g d k x ∧ ∀ y ∈ U, Entry U g d k y → y = x := by
  classical
  by_cases h : ∃ x ∈ U, ZFSet.pair k x ∈ g
  · obtain ⟨x,hx,hkx⟩ := h
    obtain ⟨n,hg⟩ := hg
    have hk : k ∈ natSet n := by
      obtain ⟨k',hk,x',_,he⟩ := hg.1 _ hkx
      exact (ZFSet.pair_inj.mp he).1 ▸ hk
    refine ⟨x,hx,Or.inl hkx,?_⟩
    intro y _ hy
    rcases hy with hy|⟨_,hy⟩
    · exact hg.functional hk hy hkx
    · exact False.elim (hy x hx hkx)
  · exact ⟨d,hd,Or.inr ⟨rfl,fun y hy hky => h ⟨y,hy,hky⟩⟩,
      fun y hy he => he.elim (fun hky => False.elim (h ⟨y,hy,hky⟩)) And.left⟩

theorem flattenFormula_spec (ω Q S C B T U d k x : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ l, finiteNaturalGraph f l ∈ e Q) (N K : ℕ)
    (hk : e k = natSet (Nat.pair N K)) :
    (flattenFormula ω Q S C B T U d k x).Eval e ↔
      ∃ E ∈ e S, ZFSet.pair (natSet N) E ∈ e B ∧
        ∃ g ∈ e C, ZFSet.pair E g ∈ e T ∧ Entry (e U) g (e d) (natSet K) (e x) := by
  simp only [flattenFormula,Formula.Eval,Formula.eval_pairMem,entryFormula_spec,cons_zero,cons_succ]
  rw [hω]
  constructor
  · rintro ⟨n,hn,j,hj,hpair,hrest⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    have he := (Formula.naturalPair_spec (ω+2) (Q+2) 1 0 (k+2)
      (cons (natSet j) (cons (natSet n) e)) hω hQ n j rfl rfl).mp hpair
    have hh := congrArg Nat.unpair (natSet_injective (hk.symm.trans he))
    simp only [Nat.unpair_pair,Prod.mk.injEq] at hh
    obtain ⟨rfl,rfl⟩ := hh
    exact hrest
  · intro h
    exact ⟨natSet N,(mem_omega _).mpr ⟨N,rfl⟩,natSet K,(mem_omega _).mpr ⟨K,rfl⟩,
      (Formula.naturalPair_spec (ω+2) (Q+2) 1 0 (k+2)
        (cons (natSet K) (cons (natSet N) e)) hω hQ N K rfl rfl).mpr hk,h⟩

theorem internally_countable_union (M U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ finiteSubsets U)
    (hB : orbitGraph E ∈ M) (hcover : ∀ p ∈ U, ∃ n, p ∈ E n)
    (hne : ∃ p, p ∈ U) : InternallyCountable M U := by
  classical
  obtain ⟨d,hd⟩ := hne
  obtain ⟨C,hCM,hC,T,hTM,hTfun,hTrange⟩ := internal_enumeration_selector M U hM hT hU
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  let S := finiteSubsets U
  let B := orbitGraph E
  have hchoice (n k : ℕ) : ∃ x ∈ U, ∃ g ∈ C,
      ZFSet.pair (E n) g ∈ T ∧ Entry U g d (natSet k) x ∧
        ∀ y ∈ U, Entry U g d (natSet k) y → y = x := by
    obtain ⟨g,hg,hEg,_⟩ := hTfun.2 _ (hE n)
    obtain ⟨x,hx,he,hu⟩ := entry_exists_unique U g d (natSet k) ((hC g).mp hg) hd
    exact ⟨x,hx,g,hg,hEg,he,hu⟩
  choose v hv g hg hEg hentry huniq using hchoice
  let f : ℕ → ZFSet.{0} := fun i => v (Nat.unpair i).1 (Nat.unpair i).2
  let e := cons ZFSet.omega (cons Q (cons S (cons C (cons B (cons T (cons U (fun _ => d)))))))
  let φ : Formula := .existsMem 1 (.existsMem 8 (.conj (.orderedPair 2 1 0)
    (flattenFormula 3 4 5 6 7 8 9 10 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|_|i
    exact hω; exact hQM; exact finiteSubsets_mem M U hM hT hU
    exact hCM; exact hB; exact hTM; exact hU; exact hM U hU d hd
  have flat (N K : ℕ) (x : ZFSet.{0}) (hx : x ∈ U) (z : ZFSet.{0}) :
      (flattenFormula 3 4 5 6 7 8 9 10 1 0).Eval
        (cons x (cons (natSet (Nat.pair N K)) (cons z e))) ↔ x = v N K := by
    rw [flattenFormula_spec 3 4 5 6 7 8 9 10 1 0 _ rfl hQ N K rfl]
    change (∃ H ∈ S, ZFSet.pair (natSet N) H ∈ B ∧
      ∃ t ∈ C, ZFSet.pair H t ∈ T ∧ Entry U t d (natSet K) x) ↔ _
    constructor
    · rintro ⟨H,_,hNH,t,_,hHt,ht⟩
      have hH := (orbitGraph_pair E N H).mp hNH
      rw [hH] at hHt
      have ht' := hTfun.functional (hE N) hHt (hEg N K)
      exact huniq N K x hx (ht' ▸ ht)
    · rintro rfl
      exact ⟨E N,hE N,(orbitGraph_pair E N _).mpr rfl,g N K,hg N K,hEg N K,hentry N K⟩
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph f := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨i,hi,x,hx,hz,hflat⟩
      obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
      have hn : natSet i = natSet (Nat.pair (Nat.unpair i).1 (Nat.unpair i).2) := by rw [Nat.pair_unpair]
      have hflat' := hflat
      rw [hn] at hflat'
      have hx' := (flat (Nat.unpair i).1 (Nat.unpair i).2 x hx z).mp hflat'
      exact (mem_orbitGraph f z).mpr ⟨i,by rw [hz,hx']⟩
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_orbitGraph f z).mp hz
      refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,f i,hv _ _,rfl,?_⟩
      have hh := (flat (Nat.unpair i).1 (Nat.unpair i).2 (f i) (hv _ _)
        (ZFSet.pair (natSet i) (f i))).mpr rfl
      simpa only [Nat.pair_unpair] using hh
  have hG : orbitGraph f ∈ M := by
    have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hU)
    have heq : (ZFSet.prod ZFSet.omega U).sep (fun z => φ.Eval (cons z e)) = orbitGraph f := by
      apply ZFSet.ext; intro z
      rw [ZFSet.mem_sep,hφ]
      exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function U f (fun _ => hv _ _)).1 z hz),hz⟩⟩
    exact heq ▸ hh
  refine ⟨orbitGraph f,hG,orbitGraph_function U f (fun _ => hv _ _),?_⟩
  intro p hp
  obtain ⟨n,hpE⟩ := hcover p hp
  have hr := hTrange (E n) (hE n) (g n 0) (hEg n 0)
  obtain ⟨k,hk,hkp⟩ := (hr.2 p hp).mp hpE
  obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
  have heq := hTfun.functional (hE n) (hEg n 0) (hEg n k)
  have hpv := huniq n k p hp (Or.inl (heq ▸ hkp))
  refine ⟨natSet (Nat.pair n k),(mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,?_⟩
  apply (orbitGraph_pair f _ p).mpr
  simpa only [f,Nat.unpair_pair] using hpv

end TuringRigidity.InternalCountableFiniteUnion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSubsetSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSubsetSequence
open TransitiveNameModel BoundedSetTheory

theorem subset_sequence (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (φ : Formula) (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M)
    (U : ℕ → ZFSet.{0}) (hU : ∀ n, U n ⊆ c)
    (hφ : ∀ n p, p ∈ c → (φ.Eval (cons p (cons (natSet n) e)) ↔ p ∈ U n)) :
    orbitGraph U ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hUM (n : ℕ) : U n ∈ M := by
    have hnM := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
    have he' : ∀ i, cons (natSet n) e i ∈ M := by
      intro i; cases i; exact hnM; exact he _
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ _ he' hc
    have heq : c.sep (fun p => φ.Eval (cons p (cons (natSet n) e))) = U n := by
      apply ZFSet.ext; intro p
      rw [ZFSet.mem_sep]
      exact ⟨fun ⟨hp,h⟩ => (hφ n p hp).mp h,fun hp => ⟨hU n hp,(hφ n p (hU n hp)).mpr hp⟩⟩
    exact heq ▸ hs
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hUQ : ∀ n, U n ∈ Q := fun n => (hQ _).mpr ⟨hUM n,hU n⟩
  let v := cons ZFSet.omega (cons Q (cons c e))
  let ren : ℕ → ℕ := fun | 0 => 0 | 1 => 2 | n+2 => n+7
  let ψ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.conj (.subset 0 5) (.allMem 5 (.iff (.member 0 1) (φ.rename ren))))))
  have hv : ∀ i, v i ∈ M := by
    intro i; rcases i with _|_|_|i; exact hω; exact hQM; exact hc; exact he i
  have renamed (p H n z : ZFSet.{0}) :
      (φ.rename ren).Eval (cons p (cons H (cons n (cons z v)))) ↔
        φ.Eval (cons p (cons n e)) := by
    rw [Formula.eval_rename_comp]
    have hh : (cons p (cons H (cons n (cons z v)))) ∘ ren = cons p (cons n e) := by
      funext i; rcases i with _|_|i <;> rfl
    rw [hh]
  have hψ (z : ZFSet.{0}) : ψ.Eval (cons z v) ↔ z ∈ orbitGraph U := by
    simp only [ψ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
      Formula.eval_allMem,Formula.eval_iff,cons_zero,cons_succ,v]
    constructor
    · rintro ⟨n,hn,H,_,hz,hH,hdef⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hHU : H = U n := by
        apply ZFSet.ext; intro p
        constructor
        · intro hp
          exact (hφ n p (hH hp)).mp ((renamed p H _ z).mp ((hdef p (hH hp)).mp hp))
        · intro hp
          exact (hdef p (hU n hp)).mpr ((renamed p H _ z).mpr ((hφ n p (hU n hp)).mpr hp))
      exact (mem_orbitGraph U z).mpr ⟨n,by rw [hz,hHU]⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph U z).mp hz
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,U n,hUQ n,rfl,hU n,?_⟩
      intro p hp
      exact (hφ n p hp).symm.trans (renamed p (U n) _ _).symm
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded ψ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hQM)
  have heq : (ZFSet.prod ZFSet.omega Q).sep (fun z => ψ.Eval (cons z v)) = orbitGraph U := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hψ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function Q U hUQ).1 z hz),hz⟩⟩
  exact heq ▸ hs

end TuringRigidity.InternalSubsetSequence

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableFamily
open TransitiveNameModel BoundedSetTheory

theorem sequence_of_graph (S B : ZFSet.{0}) (hB : FunctionGraph ZFSet.omega S B) :
    ∃ E : ℕ → ZFSet.{0}, (∀ n, E n ∈ S) ∧ orbitGraph E = B := by
  classical
  have h (n : ℕ) := hB.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
  choose E hE hpair huniq using h
  refine ⟨E,hE,?_⟩
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph E z).mp hz
    exact hpair n
  · intro hz
    obtain ⟨n,hn,x,hx,rfl⟩ := hB.1 z hz
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact (orbitGraph_pair E n x).mpr (huniq n x hx hz)

end TuringRigidity.InternalCountableFamily

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableMap
open TransitiveNameModel BoundedSetTheory

theorem pair_composite (A B C f g x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ composite A B C f g ↔
      x ∈ A ∧ y ∈ C ∧ ∃ t ∈ B, ZFSet.pair x t ∈ f ∧ ZFSet.pair t y ∈ g := by
  simp only [composite,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,ht⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,ht⟩
  · rintro ⟨hx,hy,ht⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,ht⟩

theorem composite_mem (M A B C f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    composite A B C f g ∈ M := by
  let e := cons A (cons C (cons B (cons f (fun _ => g))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hA; exact hC; exact hB; exact hf; exact hg
  simpa only [composite,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.conj (.pairMem 2 0 7) (.pairMem 0 1 8)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hC)

theorem composite_function (A B C f g : ZFSet.{0})
    (hf : FunctionGraph A B f) (hg : FunctionGraph B C g) :
    FunctionGraph A C (composite A B C f g) := by
  constructor
  · intro z hz
    exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨t,ht,hxt,_⟩ := hf.2 x hx
    obtain ⟨y,hy,hty,_⟩ := hg.2 t ht
    refine ⟨y,hy,(pair_composite A B C f g x y).mpr ⟨hx,hy,t,ht,hxt,hty⟩,?_⟩
    intro y' _ hxy'
    obtain ⟨_,_,t',_,hxt',hty'⟩ := (pair_composite A B C f g x y').mp hxy'
    have he := hf.functional hx hxt' hxt
    exact hg.functional ht (he ▸ hty') hty

theorem countable_of_surjection (M A B g : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hgM : g ∈ M)
    (hg : FunctionGraph A B g) (honto : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ g)
    (hct : InternallyCountable M A) : InternallyCountable M B := by
  obtain ⟨f,hfM,hf,hfOnto⟩ := hct
  refine ⟨composite ZFSet.omega A B f g,
    composite_mem M _ A B f g hM hT (sourceT_omega_mem M hM hT) hA hB hfM hgM,
    composite_function _ A B f g hf hg,?_⟩
  intro y hy
  obtain ⟨x,hx,hxy⟩ := honto y hy
  obtain ⟨n,hn,hnx⟩ := hfOnto x hx
  exact ⟨n,hn,(pair_composite _ A B f g n y).mpr ⟨hn,hy,x,hx,hnx,hxy⟩⟩

end TuringRigidity.InternalCountableMap

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableClosure
open TransitiveNameModel BoundedSetTheory

theorem constant_graph (A : ZFSet.{0}) :
    orbitGraph (fun _ => A) = ZFSet.prod ZFSet.omega {A} := by
  apply ZFSet.ext; intro z
  rw [mem_orbitGraph,ZFSet.mem_prod]
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,A,ZFSet.mem_singleton.mpr rfl,rfl⟩
  · rintro ⟨n,hn,x,hx,rfl⟩
    obtain rfl := ZFSet.mem_singleton.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,rfl⟩

theorem finite_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hfin : (A : Set ZFSet.{0}).Finite) (hne : ∃ x, x ∈ A) :
    InternallyCountable M A := by
  apply InternalCountableFiniteUnion.internally_countable_union M A hM hT hA (fun _ => A)
    (fun _ => (InternalFiniteSubsets.mem_finiteSubsets_iff A A).mpr ⟨fun _ h => h,hfin⟩)
    _ (fun x hx => ⟨0,hx⟩) hne
  rw [constant_graph]
  exact product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (sourceT_omega_mem M hM hT) (singleton_mem M hM hT.pairing hA)

theorem pair_retractGraph (A B d x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ retractGraph A B d ↔
      x ∈ A ∧ y ∈ B ∧ ((x ∈ B ∧ y = x) ∨ (x ∉ B ∧ y = d)) := by
  simp only [retractGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,h⟩

theorem retractGraph_mem (M A B d : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hd : d ∈ M) : retractGraph A B d ∈ M := by
  let e := cons A (cons B (fun _ => d))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hA; exact hB; exact hd
  simpa only [retractGraph,Formula.Eval,Formula.eval_orderedPair,Formula.eval_disj,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.disj (.conj (.member 1 4) (.equal 0 1))
          (.conj (.neg (.member 1 4)) (.equal 0 5)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hB)

theorem retractGraph_function (A B d : ZFSet.{0}) (hd : d ∈ B) :
    FunctionGraph A B (retractGraph A B d) := by
  classical
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    by_cases hxB : x ∈ B
    · refine ⟨x,hxB,(pair_retractGraph A B d x x).mpr ⟨hx,hxB,Or.inl ⟨hxB,rfl⟩⟩,?_⟩
      intro y _ hy
      exact ((pair_retractGraph A B d x y).mp hy).2.2.elim And.right
        (fun h => False.elim (h.1 hxB))
    · refine ⟨d,hd,(pair_retractGraph A B d x d).mpr ⟨hx,hd,Or.inr ⟨hxB,rfl⟩⟩,?_⟩
      intro y _ hy
      exact ((pair_retractGraph A B d x y).mp hy).2.2.elim
        (fun h => False.elim (hxB h.1)) And.right

theorem countable_subset (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hsub : B ⊆ A)
    (hct : InternallyCountable M A) (hne : ∃ d, d ∈ B) : InternallyCountable M B := by
  obtain ⟨d,hd⟩ := hne
  apply InternalCountableMap.countable_of_surjection M A B (retractGraph A B d) hM hT hA hB
    (retractGraph_mem M A B d hM hT hA hB (hM B hB d hd)) (retractGraph_function A B d hd) _ hct
  intro y hy
  exact ⟨y,hsub hy,(pair_retractGraph A B d y y).mpr ⟨hsub hy,hy,Or.inl ⟨hy,rfl⟩⟩⟩

end TuringRigidity.InternalCountableClosure

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteExhaustion
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets

theorem mem_initial (f : ℕ → ZFSet.{0}) (n : ℕ) (x : ZFSet.{0}) :
    x ∈ initial f n ↔ ∃ k < n, x = f k := by
  rw [initial,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,i.isLt,hi.symm⟩,fun ⟨k,hk,hx⟩ => ⟨⟨k,hk⟩,hx.symm⟩⟩

theorem initial_finite (f : ℕ → ZFSet.{0}) (n : ℕ) :
    (initial f n : Set ZFSet.{0}).Finite := by
  rw [initial,ZFSet.coe_range]
  exact Set.finite_range _

theorem initial_subset (A : ZFSet.{0}) (f : ℕ → ZFSet.{0})
    (hf : ∀ n, f n ∈ A) (n : ℕ) : initial f n ⊆ A := by
  intro x hx
  obtain ⟨k,_,rfl⟩ := (mem_initial f n x).mp hx
  exact hf k

theorem initialFormula_spec (g n x : ℕ) (e : ℕ → ZFSet.{0})
    (f : ℕ → ZFSet.{0}) (N : ℕ) (hg : e g = orbitGraph f) (hn : e n = natSet N) :
    (initialFormula g n x).Eval e ↔ e x ∈ initial f N := by
  simp only [initialFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hg,hn]
  rw [mem_initial]
  constructor
  · rintro ⟨k,hk,hkx⟩
    obtain ⟨k,hklt,rfl⟩ := (mem_natSet N k).mp hk
    exact ⟨k,hklt,(orbitGraph_pair f k _).mp hkx⟩
  · rintro ⟨k,hk,hkx⟩
    exact ⟨natSet k,(natSet_mem_natSet k N).mpr hk,(orbitGraph_pair f k _).mpr hkx⟩

theorem finite_subsets_finite (A : ZFSet.{0}) (hA : (A : Set ZFSet.{0}).Finite) :
    (finiteSubsets A : Set ZFSet.{0}).Finite := by
  apply Set.Finite.of_injOn (f := fun x : ZFSet.{0} => (x : Set ZFSet.{0}))
    (t := Set.powerset (A : Set ZFSet.{0}))
  · intro x hx
    exact (mem_finiteSubsets_iff A x).mp hx |>.1
  · intro x _ y _ hxy
    exact ZFSet.ext (fun z => Set.ext_iff.mp hxy z)
  · exact hA.powerset

theorem finite_subset_initial (A : ZFSet.{0}) (f : ℕ → ZFSet.{0})
    (honto : ∀ x ∈ A, ∃ n, x = f n) (a : ZFSet.{0}) (ha : a ∈ finiteSubsets A) :
    ∃ n, a ⊆ initial f n := by
  classical
  obtain ⟨k,v,hv,rfl⟩ := (mem_finiteSubsets A a).mp ha
  choose idx hidx using fun i => honto (v i) (hv i)
  refine ⟨Finset.univ.sup idx + 1,?_⟩
  intro x hx
  obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hx
  apply (mem_initial f _ _).mpr
  exact ⟨idx i,Nat.lt_succ_of_le (Finset.le_sup (f := idx) (Finset.mem_univ i)),hidx i⟩

theorem finite_subsets_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hct : InternallyCountable M A) :
    InternallyCountable M (finiteSubsets A) := by
  obtain ⟨g,hg,hfun,honto⟩ := hct
  obtain ⟨f,hf,hfg⟩ := InternalCountableFamily.sequence_of_graph A g hfun
  have hgf : orbitGraph f ∈ M := hfg.symm ▸ hg
  have onto : ∀ x ∈ A, ∃ n, x = f n := by
    intro x hx
    obtain ⟨n,hn,hnx⟩ := honto x hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(orbitGraph_pair f n x).mp (hfg.symm ▸ hnx)⟩
  let U := finiteSubsets A
  let E := fun n => finiteSubsets (initial f n)
  have hsub (n : ℕ) : E n ⊆ U := by
    intro a ha
    obtain ⟨hs,hfin⟩ := (mem_finiteSubsets_iff _ a).mp ha
    exact (mem_finiteSubsets_iff A a).mpr ⟨fun x hx => initial_subset A f hf n (hs hx),hfin⟩
  have hEM : orbitGraph E ∈ M := by
    apply InternalSubsetSequence.subset_sequence M U hM hT (finiteSubsets_mem M A hM hT hA)
      (.allMem 0 (initialFormula 3 2 0)) (fun _ => orbitGraph f) (fun _ => hgf) E hsub
    intro n a ha
    rw [Formula.eval_allMem]
    change (∀ x ∈ a, (initialFormula 3 2 0).Eval
      (cons x (cons a (cons (natSet n) (fun _ => orbitGraph f)))) ) ↔ _
    have heval (x : ZFSet.{0}) := initialFormula_spec 3 2 0
      (cons x (cons a (cons (natSet n) (fun _ => orbitGraph f)))) f n rfl rfl
    constructor
    · intro hs
      exact (mem_finiteSubsets_iff _ a).mpr
        ⟨fun x hx => (heval x).mp (hs x hx),((mem_finiteSubsets_iff A a).mp ha).2⟩
    · intro h x hx
      exact (heval x).mpr (((mem_finiteSubsets_iff _ a).mp h).1 hx)
  apply InternalCountableFiniteUnion.internally_countable_union M U hM hT
    (finiteSubsets_mem M A hM hT hA) E
    (fun n => (mem_finiteSubsets_iff U (E n)).mpr
      ⟨hsub n,finite_subsets_finite _ (initial_finite f n)⟩) hEM
  · intro a ha
    obtain ⟨n,hn⟩ := finite_subset_initial A f onto a ha
    exact ⟨n,(mem_finiteSubsets_iff _ a).mpr ⟨hn,((mem_finiteSubsets_iff A a).mp ha).2⟩⟩
  · exact ⟨∅,(mem_finiteSubsets_iff A ∅).mpr
      ⟨ZFSet.empty_subset A,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩⟩

end TuringRigidity.InternalFiniteExhaustion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableProduct
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteExhaustion

theorem finite_product (A B : ZFSet.{0})
    (hA : (A : Set ZFSet.{0}).Finite) (hB : (B : Set ZFSet.{0}).Finite) :
    (ZFSet.prod A B : Set ZFSet.{0}).Finite := by
  apply ((hA.prod hB).image (fun t => ZFSet.pair t.1 t.2)).subset
  intro z hz
  obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
  exact ⟨(x,y),⟨hx,hy⟩,hz.symm⟩

theorem rectangleFormula_spec (A B f g n p : ℕ) (e : ℕ → ZFSet.{0})
    (F G : ℕ → ZFSet.{0}) (N : ℕ)
    (hF : ∀ k, F k ∈ e A) (hG : ∀ k, G k ∈ e B)
    (hf : e f = orbitGraph F) (hg : e g = orbitGraph G) (hn : e n = natSet N) :
    (rectangleFormula A B f g n p).Eval e ↔ e p ∈ ZFSet.prod (initial F N) (initial G N) := by
  simp only [rectangleFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨x,_,y,_,hp,hx,hy⟩
    exact ZFSet.mem_prod.mpr ⟨x,
      (initialFormula_spec (f+2) (n+2) 1 _ F N hf hn).mp hx,y,
      (initialFormula_spec (g+2) (n+2) 0 _ G N hg hn).mp hy,hp⟩
  · intro hp
    obtain ⟨x,hx,y,hy,hp⟩ := ZFSet.mem_prod.mp hp
    exact ⟨x,initial_subset (e A) F hF N hx,y,initial_subset (e B) G hG N hy,hp,
      (initialFormula_spec (f+2) (n+2) 1 _ F N hf hn).mpr hx,
      (initialFormula_spec (g+2) (n+2) 0 _ G N hg hn).mpr hy⟩

theorem product_countable (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : InternallyCountable M A) (hcB : InternallyCountable M B) :
    InternallyCountable M (ZFSet.prod A B) := by
  obtain ⟨f,hf,hff,hfo⟩ := hcA
  obtain ⟨g,hg,hgf,hgo⟩ := hcB
  obtain ⟨F,hF,hFf⟩ := InternalCountableFamily.sequence_of_graph A f hff
  obtain ⟨G,hG,hGg⟩ := InternalCountableFamily.sequence_of_graph B g hgf
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  let E := fun n => ZFSet.prod (initial F n) (initial G n)
  have hsub (n : ℕ) : E n ⊆ ZFSet.prod A B := by
    intro z hz
    obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
    exact ZFSet.mem_prod.mpr ⟨x,initial_subset A F hF n hx,y,initial_subset B G hG n hy,hz⟩
  have hgraph : orbitGraph E ∈ M := by
    let e := cons A (cons B (cons f (fun _ => g)))
    have he : ∀ i, e i ∈ M := by
      intro i; rcases i with _|_|_|i
      exact hA; exact hB; exact hf; exact hg
    exact InternalSubsetSequence.subset_sequence M _ hM hT hprod
      (rectangleFormula 2 3 4 5 1 0) e he E hsub
      (fun n _ _ => rectangleFormula_spec 2 3 4 5 1 0 _ F G n hF hG hFf.symm hGg.symm rfl)
  apply InternalCountableFiniteUnion.internally_countable_union M _ hM hT hprod E
    (fun n => (mem_finiteSubsets_iff _ (E n)).mpr
      ⟨hsub n,finite_product _ _ (initial_finite F n) (initial_finite G n)⟩) hgraph
  · intro z hz
    obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨i,hi,hix⟩ := hfo x hx
    obtain ⟨j,hj,hjy⟩ := hgo y hy
    obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    refine ⟨max i j + 1,ZFSet.mem_prod.mpr ⟨x,?_,y,?_,hz⟩⟩
    · exact (mem_initial F _ x).mpr
        ⟨i,Nat.lt_succ_of_le (Nat.le_max_left i j),(orbitGraph_pair F i x).mp (hFf.symm ▸ hix)⟩
    · exact (mem_initial G _ y).mpr
        ⟨j,Nat.lt_succ_of_le (Nat.le_max_right i j),(orbitGraph_pair G j y).mp (hGg.symm ▸ hjy)⟩
  · exact ⟨ZFSet.pair (F 0) (G 0),ZFSet.pair_mem_prod.mpr ⟨hF 0,hG 0⟩⟩

theorem product_empty_left (B : ZFSet.{0}) : ZFSet.prod ∅ B = ∅ := by
  apply ZFSet.ext; intro z; simp [ZFSet.mem_prod]

theorem product_empty_right (A : ZFSet.{0}) : ZFSet.prod A ∅ = ∅ := by
  apply ZFSet.ext; intro z; simp [ZFSet.mem_prod]

theorem product_countable_or_empty (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : A = ∅ ∨ InternallyCountable M A) (hcB : B = ∅ ∨ InternallyCountable M B) :
    ZFSet.prod A B = ∅ ∨ InternallyCountable M (ZFSet.prod A B) := by
  rcases hcA with rfl|hcA
  · exact Or.inl (product_empty_left B)
  rcases hcB with rfl|hcB
  · exact Or.inl (product_empty_right A)
  exact Or.inr (product_countable M A B hM hT hA hB hcA hcB)

theorem omega_countable (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternallyCountable M ZFSet.omega := by
  have hω := sourceT_omega_mem M hM hT
  have hn (n : ℕ) : natSet.{0} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  let e : ℕ → ZFSet.{0} := fun _ => ZFSet.omega
  let φ : Formula := .existsMem 1 (.orderedPair 1 0 0)
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph natSet := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,mem_orbitGraph]
    exact ⟨fun ⟨x,hx,hz⟩ => by obtain ⟨n,rfl⟩ := (mem_omega x).mp hx; exact ⟨n,hz⟩,
      fun ⟨n,hz⟩ => ⟨natSet n,hn n,hz⟩⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e (fun _ => hω)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hω)
  have heq : (ZFSet.prod ZFSet.omega ZFSet.omega).sep (fun z => φ.Eval (cons z e)) =
      orbitGraph natSet := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function _ natSet hn).1 z hz),hz⟩⟩
  refine ⟨orbitGraph natSet,heq ▸ hs,orbitGraph_function _ natSet hn,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact ⟨natSet n,hn n,(orbitGraph_pair natSet n _).mpr rfl⟩

end TuringRigidity.InternalCountableProduct

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CountedCohenConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountedCohenConditions
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteExhaustion
open InternalCountableProduct InternalCountableClosure CohenGroundPoset

theorem finite_subsets_countable_or_empty (M A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M)
    (hct : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (finiteSubsets A) := by
  rcases hct with rfl|hct
  · apply finite_countable M _ hM hT (finiteSubsets_mem M ∅ hM hT hA)
      (finite_subsets_finite ∅ (by simpa only [ZFSet.coe_empty] using Set.finite_empty))
    exact ⟨∅,(mem_finiteSubsets_iff ∅ ∅).mpr
      ⟨ZFSet.empty_subset ∅,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩⟩
  · exact finite_subsets_countable M A hM hT hA hct

theorem empty_condition (A : ZFSet.{0}) : ∅ ∈ conditions A := by
  apply (mem_conditions A ∅).mpr
  refine ⟨(mem_finiteSubsets_iff _ ∅).mpr
    ⟨ZFSet.empty_subset _,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩,?_⟩
  intro x _ b _ c _ hb
  exact False.elim (ZFSet.notMem_empty _ hb)

theorem alphabet_countable (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternallyCountable M InternalCohen.alphabet := by
  apply finite_countable M _ hM hT (InternalCohen.alphabet_mem M hM hT)
  · have he : (InternalCohen.alphabet : Set ZFSet.{0}) = Set.range InternalCohen.bitSet := by
      ext x
      exact (InternalCohen.mem_alphabet x).trans ⟨fun ⟨b,hb⟩ => ⟨b,hb.symm⟩,
        fun ⟨b,hb⟩ => ⟨b,hb.symm⟩⟩
    rw [he]
    exact Set.finite_range _
  · exact ⟨InternalCohen.bitSet false,(InternalCohen.mem_alphabet _).mpr ⟨false,rfl⟩⟩

theorem conditions_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hct : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (conditions A) := by
  have hB := InternalCohen.alphabet_mem M hM hT
  have hP := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  have hpc := product_countable_or_empty M A InternalCohen.alphabet hM hT hA hB
    hct (Or.inr (alphabet_countable M hM hT))
  have hfc := finite_subsets_countable_or_empty M _ hM hT hP hpc
  exact countable_subset M _ _ hM hT (finiteSubsets_mem M _ hM hT hP)
    (conditions_mem M A hM hT hA) (fun _ hp => ((mem_conditions A _).mp hp).1)
    hfc ⟨∅,empty_condition A⟩

theorem many_column_conditions_countable (M C : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    InternallyCountable M (conditions (ZFSet.prod C ZFSet.omega)) := by
  have hω := sourceT_omega_mem M hM hT
  exact conditions_countable M _ hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hC hω)
    (product_countable_or_empty M C ZFSet.omega hM hT hC hω hct
      (Or.inr (omega_countable M hM hT)))

end TuringRigidity.CountedCohenConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientCountability
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalQuotientGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem countability_upward (M N c : ZFSet.{0}) (hMN : M ⊆ N)
    (hct : InternallyCountable M c) : InternallyCountable N c := by
  obtain ⟨E,hE,hfun,honto⟩ := hct
  exact ⟨E,hMN hE,hfun,honto⟩

end TuringRigidity.InternalQuotientCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountedOriginalRealQuotient
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountedOriginalRealQuotient
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_counted_quotient (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M)
    (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
          (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode (conditions (ZFSet.prod C ZFSet.omega)) U) ∧
          (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
          A = InternalGeneratedAlgebra.generated (conditions (ZFSet.prod C ZFSet.omega)) B Q
            (InternalBooleanBits.seeds (conditions (ZFSet.prod C ZFSet.omega)) B E) ∧
          Closed (conditions (ZFSet.prod C ZFSet.omega)) B Q A ∧
          ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
            ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
            ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
              AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
              let J := InternalCohenProjectedGeneric.projected _ _ hBA G
              let X := τ.val G.carrier
              ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
                σ.val H.carrier = X ∧
                genericExtensionSet M (positive A) H.carrier = RealGeneratedModel.hull M X ∧
                RealGeneratedModel.Contains M X (RealGeneratedModel.hull M X) ∧
                let q := InternalQuotientConditions.conditions (conditions (ZFSet.prod C ZFSet.omega)) A
                  (genericFilterSet (positive A) H.carrier)
                q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈ RealGeneratedModel.hull M X ∧
                InternallyCountable (RealGeneratedModel.hull M X) q ∧
                ∃ Gq : GenericFilter (Conditions q), AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) Gq ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericFilterSet q Gq.carrier =
                    genericFilterSet (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier ⊆
                    genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                  ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
                    label q r = label _ (InternalCohenFactor.project _ _ hBA p) := by
  obtain ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,hall⟩ :=
    OriginalRealQuotientModel.original_name_quotient M K hM hT hK τ hτ
  have hcM := (manyColumn_internal M C hM hT hC).1
  have hcount := CountedCohenConditions.many_column_conditions_countable M C hM hT hC hct
  refine ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨H,hHG,hval,hHull,hprop,hq,ho,Gq,hGq,hext,hcode,hsub,hcond⟩ := hall G hG hreal
  refine ⟨H,hHG,hval,hHull,hprop,hq,ho,?_,Gq,hGq,hext,hcode,hsub,hcond⟩
  apply InternalCountableClosure.countable_subset _ _ _ hprop.1 hprop.2.1
    (hprop.2.2.1 hcM) hq (InternalQuotientConditions.conditions_subset _ A _)
    (InternalQuotientCountability.countability_upward M _ _ hprop.2.2.1 hcount)
  obtain ⟨p,_⟩ := Gq.nonempty
  exact ⟨label _ p,label_mem _ p⟩

end TuringRigidity.CountedOriginalRealQuotient

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OriginalRealFullIteration
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealFullIteration
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_full_iteration_oai (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M)
    (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
          (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode (conditions (ZFSet.prod C ZFSet.omega)) U) ∧
          (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
          A = InternalGeneratedAlgebra.generated (conditions (ZFSet.prod C ZFSet.omega)) B Q
            (InternalBooleanBits.seeds (conditions (ZFSet.prod C ZFSet.omega)) B E) ∧
          Closed (conditions (ZFSet.prod C ZFSet.omega)) B Q A ∧
          ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
            ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
            ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
              AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
              let J := InternalCohenProjectedGeneric.projected _ _ hBA G
              let X := τ.val G.carrier
              let D := ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega
              let L := InternalCohenProjectedGeneric.projected _ D
                (fun _ h => (ZFSet.mem_sdiff.mp h).1) G
              ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
                σ.val H.carrier = X ∧
                genericExtensionSet M (positive A) H.carrier = RealGeneratedModel.hull M X ∧
                RealGeneratedModel.Contains M X (RealGeneratedModel.hull M X) ∧
                let q := InternalQuotientConditions.conditions (conditions (ZFSet.prod C ZFSet.omega)) A
                  (genericFilterSet (positive A) H.carrier)
                q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈ RealGeneratedModel.hull M X ∧
                InternallyCountable (RealGeneratedModel.hull M X) q ∧
                ∃ Gq : GenericFilter (Conditions q), AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) Gq ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericFilterSet q Gq.carrier =
                    genericFilterSet (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  AtomicForcing.GroundGeneric
                    (genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier) L ∧
                  genericExtensionSet (genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier)
                    (conditions D) L.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                  modelReals (genericExtensionSet
                    (genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier)
                    (conditions D) L.carrier) =
                    modelReals (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier) ∧
                  ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
                    label q r = label _ (InternalCohenFactor.project _ _ hBA p) := by
  obtain ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,hall⟩ :=
    CountedOriginalRealQuotient.original_name_counted_quotient M K hM hT hK τ hτ
  have hω := sourceT_omega_mem M hM hT
  have hKM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hCM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hC hω
  refine ⟨C,hC,hCK,hct,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,hAe,hA,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨H,hHG,hval,hHull,hprop,hq,ho,hcount,Gq,hGq,hext,hcode,_,hcond⟩ := hall G hG hreal
  refine ⟨H,hHG,hval,hHull,hprop,hq,ho,hcount,Gq,hGq,hext,hcode,?_,?_,?_,hcond⟩
  · rw [hext]
    exact CohenUntouchedGeneric.untouched_ground_generic M _ _ hM hT hKM hCM hBA G hG
  · rw [hext]
    exact CohenFactorIteration.extension_eq M _ _ hM hT hKM hCM hBA G hG
  · rw [hext]
    exact congrArg modelReals (CohenFactorIteration.extension_eq M _ _ hM hT hKM hCM hBA G hG)

end TuringRigidity.OriginalRealFullIteration

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration_oai := @OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration_oai
