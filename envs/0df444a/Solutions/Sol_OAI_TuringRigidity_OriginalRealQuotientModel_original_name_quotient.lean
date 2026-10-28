-- Prove2me | solution 1 for OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:27:57.155994+00:00
-- url     : https://prove2.me/submissions/cd66375a-0caa-4921-ba99-1c3c6c285a61

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_CohenNiceNameConstruction_internal_nice_name
import Theorems.Thm_OAI_TuringRigidity_InternalBooleanIntermediate_internal_boolean_intermediate
import Theorems.Thm_OAI_TuringRigidity_RealGeneratedModel_hull_properties
import Theorems.Thm_OAI_TuringRigidity_RealGeneratedModel_projected_extension_eq_hull

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

theorem supported_condition (A B p : ZFSet.{0}) (hBA : B ⊆ A)
    (hp : p ∈ conditions A) (hs : supportSet A p ⊆ B) :
    p ∈ conditions B ∧ restrict B p = p := by
  have he : restrict B p = p := by
    apply ZFSet.ext; intro z
    rw [mem_restrict]
    refine ⟨And.left,fun hz => ⟨hz,?_⟩⟩
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (condition_subset A p hp hz)
    exact ZFSet.pair_mem_prod.mpr ⟨hs (ZFSet.mem_sep.mpr ⟨hx,b,hb,hz⟩),hb⟩
  exact ⟨he ▸ restrict_condition A B p hBA hp,he⟩

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

theorem nice_value_mem_projected (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hBA : B ⊆ A) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ conditions B) (hgraph : orbitGraph E ∈ M)
    (G : GenericFilter (Conditions (conditions A))) :
    (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier ∈
      genericExtensionSet M (conditions B) (projected A B hBA G).carrier := by
  rw [←nice_value_projected A B hBA E (fun n => (hE n).2) G]
  have hn := InternalNiceName.nice_internal M hM hT (conditions_mem M B hM hT hB) E hE hgraph
  change _ ∈ (genericExtensionSet M (conditions B) (projected A B hBA G).carrier : Set ZFSet.{0})
  rw [genericExtensionSet_coe]
  exact ⟨InternalNiceName.nice E,hn,rfl⟩

end TuringRigidity.InternalCohenSupportedValue

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalColumnProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalColumnProjection
open TransitiveNameModel BoundedSetTheory InternalCountableMap

theorem mem_columns (K S x : ZFSet.{0}) :
    x ∈ columns K S ↔ x ∈ K ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ S := ZFSet.mem_sep

theorem columns_mem (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hS : S ∈ M) : columns K S ∈ M := by
  let e := cons ZFSet.omega (fun _ => S)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i; exact sourceT_omega_mem M hM hT; exact hS
  simpa only [columns,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 1 0 3)) e he hK

theorem support_subset_columns (K S : ZFSet.{0}) (hS : S ⊆ ZFSet.prod K ZFSet.omega) :
    S ⊆ ZFSet.prod (columns K S) ZFSet.omega := by
  intro z hz
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp (hS hz)
  exact ZFSet.pair_mem_prod.mpr ⟨(mem_columns K S x).mpr ⟨hx,n,hn,hz⟩,hn⟩

theorem pair_projection (K S s x : ZFSet.{0}) :
    ZFSet.pair s x ∈ projection K S ↔
      s ∈ S ∧ x ∈ columns K S ∧ ∃ n ∈ ZFSet.omega, s = ZFSet.pair x n := by
  simp only [projection,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,s',hs,x',hx,he,hn⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hs,hx,hn⟩
  · rintro ⟨hs,hx,hn⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hs,hx⟩,s,hs,x,hx,rfl,hn⟩

theorem projection_mem (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hS : S ∈ M) : projection K S ∈ M := by
  have hC := columns_mem M K S hM hT hK hS
  let e := cons S (cons (columns K S) (fun _ => ZFSet.omega))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hS; exact hC; exact sourceT_omega_mem M hM hT
  simpa only [projection,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.orderedPair 2 1 0))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hS hC)

theorem projection_function (K S : ZFSet.{0}) (hS : S ⊆ ZFSet.prod K ZFSet.omega) :
    FunctionGraph S (columns K S) (projection K S) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro s hs
    obtain ⟨x,hx,n,hn,he⟩ := ZFSet.mem_prod.mp (hS hs)
    have hxC : x ∈ columns K S := (mem_columns K S x).mpr ⟨hx,n,hn,he ▸ hs⟩
    refine ⟨x,hxC,(pair_projection K S s x).mpr ⟨hs,hxC,n,hn,he⟩,?_⟩
    intro y _ hsy
    obtain ⟨_,_,m,_,hm⟩ := (pair_projection K S s y).mp hsy
    exact (ZFSet.pair_inj.mp (hm.symm.trans he)).1

theorem projection_onto (K S : ZFSet.{0}) :
    ∀ x ∈ columns K S, ∃ s ∈ S, ZFSet.pair s x ∈ projection K S := by
  intro x hx
  obtain ⟨_,n,hn,hs⟩ := (mem_columns K S x).mp hx
  exact ⟨ZFSet.pair x n,hs,(pair_projection K S _ x).mpr ⟨hs,hx,n,hn,rfl⟩⟩

theorem columns_counted (M K S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hS : S ∈ M) (hsub : S ⊆ ZFSet.prod K ZFSet.omega)
    (hct : S = ∅ ∨ InternallyCountable M S) :
    columns K S ∈ M ∧ columns K S ⊆ K ∧
      S ⊆ ZFSet.prod (columns K S) ZFSet.omega ∧
      (columns K S = ∅ ∨ InternallyCountable M (columns K S)) := by
  refine ⟨columns_mem M K S hM hT hK hS,fun _ h => (mem_columns K S _).mp h |>.1,
    support_subset_columns K S hsub,?_⟩
  rcases hct with he|hc
  · left
    apply ZFSet.ext; intro x
    simp only [columns,he,ZFSet.mem_sep,ZFSet.notMem_empty,and_false,exists_false]
  · right
    exact countable_of_surjection M S (columns K S) (projection K S) hM hT hS
      (columns_mem M K S hM hT hK hS) (projection_mem M K S hM hT hK hS)
      (projection_function K S hsub) (projection_onto K S) hc

end TuringRigidity.InternalColumnProjection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenColumnReading
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenColumnReading
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset CohenInternalSupport InternalCohenRestriction InternalCohenPartition
open InternalCohenFactor InternalCohenProjectedGeneric InternalCohenSupportedValue
open InternalColumnProjection
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem internal_column_reading (M K : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K,
      (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        (InternalNiceName.nice E : Name (Conditions (conditions (ZFSet.prod C ZFSet.omega)))).encode
          (label (conditions (ZFSet.prod C ZFSet.omega))) ∈ M ∧
        ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
        ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
          AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
          AtomicForcing.GroundGeneric M (projected _ _ hBA G) ∧
          (InternalNiceName.nice E : Name (Conditions (conditions (ZFSet.prod C ZFSet.omega)))).val
            (projected _ _ hBA G).carrier = τ.val G.carrier ∧
          τ.val G.carrier ∈ genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega))
            (projected _ _ hBA G).carrier ∧
          ∀ p ∈ G.carrier, project _ _ hBA p ∈ (projected _ _ hBA G).carrier := by
  let A := ZFSet.prod K ZFSet.omega
  have hω := sourceT_omega_mem M hM hT
  have hA : A ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  obtain ⟨E,hgraph,hE,_,⟨S,hSM,hSA,hS,hct⟩,hval⟩ :=
    CohenNiceNameConstruction.internal_nice_name M A hM hT hA τ hτ
  let C := columns K S
  obtain ⟨hCM,hCK,hSC,hCct⟩ := columns_counted M K S hM hT hK hSM hSA hct
  let B := ZFSet.prod C ZFSet.omega
  have hBM : B ∈ M := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hCM hω
  have hBA : B ⊆ A := by
    intro z hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨hCK hx,hn⟩
  have hEcB (n : ℕ) : E n ∈ M ∧ E n ⊆ conditions B := by
    refine ⟨(hE n).1,?_⟩
    intro p hp
    have hpA : p ∈ conditions A := (ZFSet.mem_sep.mp ((hE n).2.1 hp)).1
    apply (supported_condition A B p hBA hpA ?_).1
    intro x hx
    exact hSC ((hS x).mpr ⟨n,p,hp,hx⟩)
  refine ⟨C,hCM,hCK,hCct,E,hgraph,hEcB,
    InternalNiceName.nice_internal M hM hT (conditions_mem M B hM hT hBM) E hEcB hgraph,
    hBA,?_⟩
  intro G hG hreal
  have he := hval G hG hreal
  refine ⟨projected_groundGeneric M A B hM hT hA hBM hBA G hG,
    (nice_value_projected A B hBA E (fun n => (hEcB n).2) G).trans he,?_,
    fun p hp => projected_contains A B hBA G hp⟩
  rw [←he]
  exact nice_value_mem_projected M A B hM hT hBM hBA E hEcB hgraph G

end TuringRigidity.InternalCohenColumnReading

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanProjection
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalGeneratedAlgebra

theorem project_le_iff (c A U V : ZFSet.{0}) (hUc : U ⊆ c) (hV : V ∈ A) :
    project c A U ⊆ V ↔ U ⊆ V := by
  constructor
  · intro h p hp; exact h (subset_project c A U hUc hp)
  · intro h; exact inf_subset c _ (ZFSet.mem_sep.mpr ⟨hV,h⟩)

theorem project_nonempty (c A U : ZFSet.{0}) (hUc : U ⊆ c) (hU : U ≠ ∅) : project c A U ≠ ∅ := by
  intro hp
  apply hU
  apply ZFSet.ext
  intro p
  constructor
  · intro h
    have hx := subset_project c A U hUc h
    rw [hp] at hx
    exact hx
  · exact fun h => False.elim (ZFSet.notMem_empty p h)

end TuringRigidity.InternalBooleanProjection

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanGraph
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalBooleanProjection

theorem inclusionOrder_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) : inclusionOrder A ∈ M := by
  have hp := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hA
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.subset 1 0))))
    (fun _ => A) (fun _ => hA) hp
  simpa only [inclusionOrder,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
    cons_zero,cons_succ] using hs

theorem pair_inclusionOrder (A U V : ZFSet.{0}) : ZFSet.pair U V ∈ inclusionOrder A ↔
    U ∈ A ∧ V ∈ A ∧ U ⊆ V := by
  rw [inclusionOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,U',hU,V',hV,he,hp⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hU,hV,hp⟩
  · rintro ⟨hU,hV,hp⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨U,hU,V,hV,rfl⟩,U,hU,V,hV,rfl,hp⟩

end TuringRigidity.InternalBooleanGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanDense
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanDense
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem basicCode_le_iff (c p U : ZFSet.{0}) (hp : p ∈ c) (hU : IsCode c U) :
    basicCode c p ⊆ U ↔ p ∈ U := by
  constructor
  · intro h; exact h (mem_basicCode c p hp)
  · intro hpU
    apply (regular_le_iff c _ U (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c {p}) hU).mpr
    intro q hq
    obtain ⟨hqc,r,hr,hrq⟩ := ZFSet.mem_sep.mp hq
    have hrp := ZFSet.mem_singleton.mp hr
    subst r
    exact code_lower c U hU p hpU q hqc hrq

theorem dense_preimage (M c B Q A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hD : DenseCodes A D) : Dense {p : Conditions c | label c p ∈ ZFSet.sUnion D} := by
  classical
  intro p
  let b := basicCode c (label c p)
  have hbM : b ∈ M := basicCode_mem M c _ hM hT hc (label_mem c p)
  have hbc : IsCode c b := regular_isCode c _
  have hpb : label c p ∈ b := mem_basicCode c _ (label_mem c p)
  have hb0 : b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
  have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
  obtain ⟨V,hVD,hVA,hV0,hVP⟩ := hD _ hPA (project_nonempty c A b hbc.1 hb0)
  have hVc := ((hB V).mp (hA.1 hVA)).2
  have hex : ∃ q ∈ V, label c p ⊆ q := by
    by_contra hn
    have hpN : label c p ∈ neg c V := ZFSet.mem_sep.mpr
      ⟨label_mem c p,fun q hq hpq => hn ⟨q,hq,hpq⟩⟩
    have hbN : b ⊆ neg c V := (basicCode_le_iff c _ _ (label_mem c p) (neg_isCode c V hVc)).mpr hpN
    have hPN := (project_le_iff c A b _ hbc.1 (hA.2.1 V hVA)).mpr hbN
    apply hV0
    apply ZFSet.ext
    intro q
    constructor
    · intro hq
      have hqN := hPN (hVP hq)
      exact False.elim ((ZFSet.mem_sep.mp hqN).2 q hq (fun _ h => h))
    · exact fun h => False.elim (ZFSet.notMem_empty q h)
  obtain ⟨q,hq,hpq⟩ := hex
  obtain ⟨q,rfl⟩ := label_surjective c (hVc.1 hq)
  exact ⟨q,hpq,ZFSet.mem_sUnion.mpr ⟨V,hVD,hq⟩⟩

theorem ground_meets_dense_codes (M c B Q A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M) (hDM : D ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hD : DenseCodes A D) (G : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) : ∃ U ∈ D, Hit G U := by
  obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion D) (union_mem M hM hT.union hDM)
    (dense_preimage M c B Q A D hM hT hc hBM hAM hB hQ hA hD)
  obtain ⟨U,hU,hpU⟩ := ZFSet.mem_sUnion.mp hpD
  exact ⟨U,hU,p,hp,hpU⟩

end TuringRigidity.InternalBooleanDense

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalProjectedGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem positive_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) : positive A ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 0 (.equal 0 0)) (fun _ => A) (fun _ => hA) hA
  have he : A.sep (fun U => (Formula.existsMem 0 (.equal 0 0)).Eval (cons U (fun _ => A))) = positive A := by
    apply ZFSet.ext
    intro U
    simp only [positive,ZFSet.mem_sep,Formula.Eval,cons_zero]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨p,hp,_⟩ h0
      exact ZFSet.notMem_empty p (h0 ▸ hp)
    · intro hn
      obtain h0 | ⟨p,hp⟩ := ZFSet.eq_empty_or_nonempty U
      · exact False.elim (hn h0)
      · exact ⟨p,hp,True.intro⟩
  exact he ▸ hs

attribute [local instance] codeOrder codePreorder

theorem projected_ground_generic (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (projected M c B Q A hM hT hc hBM hAM hB hQ hA G) := by
  intro D hDM hD
  let D' := (positive A).sep (fun U => U ∈ D)
  have hD'M : D' ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded
      (.member 0 1) (fun _ => D) (fun _ => hDM) (positive_mem M A hM hT hAM)
    simpa only [D',Formula.Eval,cons_zero,cons_succ] using hs
  have hd : DenseCodes A D' := by
    intro U hUA hU0
    obtain ⟨p,hp⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hUA,hU0⟩)
    obtain ⟨q,hqp,hqD⟩ := hD p
    refine ⟨label (positive A) q,ZFSet.mem_sep.mpr ⟨label_mem _ q,hqD⟩,
      (label_info A q).1,(label_info A q).2,?_⟩
    change label (positive A) q ⊆ label (positive A) p at hqp
    rwa [hp] at hqp
  obtain ⟨U,hUD,hUG⟩ := ground_meets_dense_codes M c B Q A D' hM hT hc hBM hAM hD'M hB hQ hA hd G hG
  obtain ⟨hUp,hUD⟩ := ZFSet.mem_sep.mp hUD
  obtain ⟨p,hp⟩ := label_surjective (positive A) hUp
  exact ⟨p,(show Hit G (label (positive A) p) from hp.symm ▸ hUG),hp.symm ▸ hUD⟩

theorem projected_order_code (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) :
    InternalBooleanGraph.inclusionOrder (positive A) ∈ M ∧
      ∀ p q : Conditions (positive A),
        ZFSet.pair (label (positive A) p) (label (positive A) q) ∈
          InternalBooleanGraph.inclusionOrder (positive A) ↔ p ≤ q := by
  refine ⟨InternalBooleanGraph.inclusionOrder_mem M _ hM hT (positive_mem M A hM hT hA),?_⟩
  intro p q
  rw [InternalBooleanGraph.pair_inclusionOrder]
  exact ⟨fun h => h.2.2,fun h => ⟨label_mem _ p,label_mem _ q,h⟩⟩

end TuringRigidity.InternalProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_RestrictedForcingFilter
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RestrictedForcingFilter
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem original_condition (c q : ZFSet.{0}) (hqc : q ⊆ c)
    (G : GenericFilter (Conditions c)) (hGq : ∀ p ∈ G.carrier, label c p ∈ q)
    (p : Conditions c) (hp : p ∈ G.carrier) :
    ∃ r ∈ (restrict c q hqc G hGq).carrier, label q r = label c p := by
  obtain ⟨r,hr⟩ := label_surjective q (hGq p hp)
  have he : inclusion c q hqc r = p := label_injective c ((label_inclusion c q hqc r).trans hr)
  exact ⟨r,(show inclusion c q hqc r ∈ G.carrier from he.symm ▸ hp),hr⟩

theorem filterSet_eq (c q : ZFSet.{0}) (hqc : q ⊆ c)
    (G : GenericFilter (Conditions c)) (hGq : ∀ p ∈ G.carrier, label c p ∈ q) :
    genericFilterSet q (restrict c q hqc G hGq).carrier = genericFilterSet c G.carrier := by
  apply ZFSet.ext; intro x
  rw [mem_genericFilterSet,mem_genericFilterSet]
  constructor
  · rintro ⟨p,hp,hx⟩
    exact ⟨inclusion c q hqc p,hp,(label_inclusion c q hqc p).trans hx⟩
  · rintro ⟨p,hp,hx⟩
    obtain ⟨r,hr,he⟩ := original_condition c q hqc G hGq p hp
    exact ⟨r,hr,he.trans hx⟩

end TuringRigidity.RestrictedForcingFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanTop
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanTop
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
open InternalBooleanSyntax InternalBooleanProjection InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem top_mem_part (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A) : c ∈ A := by
  have h0 : (∅ : ZFSet.{0}) ∈ M := hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero
  have h := closed_inf M c B Q A ∅ hM hT hc hBM hB hQ hA h0
    (fun x hx => False.elim (ZFSet.notMem_empty x hx))
  have he : infCode c ∅ = c := by
    apply ZFSet.ext; intro p
    simp only [infCode,ZFSet.mem_sep,ZFSet.notMem_empty,false_implies,implies_true,and_true]
  rwa [he] at h

theorem label_booleanTop (c A : ZFSet.{0}) (hcA : c ∈ A) (hc0 : c ≠ ∅) :
    @label (positive A) (booleanTop c A hcA hc0).top = c :=
  Classical.choose_spec (label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hcA,hc0⟩))

theorem top_in_filter (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hAc : ∀ U ∈ A, U ⊆ c) (ht : label (positive A) ⊤ = c)
    (H : GenericFilter (Conditions (positive A))) : ⊤ ∈ H.carrier := by
  obtain ⟨p,hp⟩ := H.nonempty
  apply H.upper (q := ⊤) _ hp
  change label (positive A) p ⊆ label (positive A) ⊤
  rw [ht]
  exact hAc _ (label_info A p).1

end TuringRigidity.InternalBooleanTop

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanExtension
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem hitSet_mem (N A g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hg : g ∈ N) : hitSet A g ∈ N := by
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 1 (.member 0 1)) (fun _ => g) (fun _ => hg)
    (positive_mem N A hN hT hA)
  simpa only [hitSet,Formula.Eval,cons_zero,cons_succ] using hs

theorem projected_filterSet (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      hitSet A (genericFilterSet c G.carrier) := by
  apply ZFSet.ext; intro U
  rw [mem_genericFilterSet,hitSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨p,hp,hpq⟩ := hq
    exact ⟨label_mem _ q,label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hpq⟩
  · rintro ⟨hU,p,hp,hpU⟩
    obtain ⟨q,rfl⟩ := label_surjective (positive A) hU
    obtain ⟨r,hr,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,⟨r,hr,hpU⟩,rfl⟩

theorem projected_extension_subset_model (M N c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hgN : genericFilterSet c G.carrier ∈ N) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆ N := by
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  rw [projected_filterSet M c B Q A hM hT hc hBM hAM hB hQ hA G]
  exact hitSet_mem N A _ hN hTN (hMN hAM) hgN

theorem projected_extension_subset_original (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈ G.carrier) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆
        genericExtensionSet M c G.carrier := by
  have hN := genericExtensionSet_transitive M c hM G.carrier
  have hTN := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair c) G hG hTop
  have hMN := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hTop
  apply projected_extension_subset_model M _ c B Q A hM hT hN hTN hMN hc hBM hAM hB hQ hA G
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hTop

end TuringRigidity.InternalBooleanExtension

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientConditions
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem cover_eq_project (c A p : ZFSet.{0}) (hp : p ∈ c)
    (hA : ∀ U ∈ A, IsCode c U) : cover c A p = project c A (basicCode c p) := by
  apply ZFSet.ext; intro r
  simp only [cover,project,infCode,uppers,ZFSet.mem_sep]
  apply and_congr_right; intro _
  constructor
  · intro h U hU
    exact h U hU.1 ((basicCode_le_iff c p U hp (hA U hU.1)).mp hU.2)
  · intro h U hU hpU
    exact h U ⟨hU,(basicCode_le_iff c p U hp (hA U hU)).mpr hpU⟩

theorem coverFormula_spec (c A p V : ℕ) (e : ℕ → ZFSet.{0}) :
    (coverFormula c A p V).Eval e ↔ e V = cover (e c) (e A) (e p) := by
  simp only [coverFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  constructor
  · rintro ⟨hVc,hV⟩
    exact ZFSet.ext (fun r => (Iff.intro
      (fun hr => ⟨hVc hr,(hV r (hVc hr)).mp hr⟩)
      (fun hr => (hV r hr.1).mpr hr.2)).trans ZFSet.mem_sep.symm)
  · intro h; rw [h]
    exact ⟨fun _ hr => (ZFSet.mem_sep.mp hr).1,fun r hr =>
      ZFSet.mem_sep.trans (and_iff_right hr)⟩

theorem conditions_mem (N c A h : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hA : A ∈ N) (hh : h ∈ N)
    (hAc : ∀ U ∈ A, IsCode c U) : conditions c A h ∈ N := by
  let e := cons c (cons A (fun _ => h))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|i; exact hc; exact hA; exact hh
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 3 (coverFormula 2 3 1 0)) e he hc
  have heq : c.sep (fun p => (Formula.existsMem 3 (coverFormula 2 3 1 0)).Eval (cons p e)) =
      conditions c A h := by
    apply ZFSet.ext; intro p
    simp only [conditions,ZFSet.mem_sep,Formula.Eval,coverFormula_spec,cons_zero,cons_succ,e]
    apply and_congr_right; intro hp
    rw [cover_eq_project c A p hp hAc]
    exact ⟨fun ⟨V,hV,he⟩ => he ▸ hV,fun hv => ⟨_,hv,rfl⟩⟩
  exact heq ▸ hs

end TuringRigidity.InternalQuotientConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientLifting
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientLifting
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem extension_in_code (c A : ZFSet.{0}) (hAc : ∀ U ∈ A, IsCode c U)
    (hneg : ∀ U ∈ A, neg c U ∈ A) (p : Conditions c)
    (V : ZFSet.{0}) (hVA : V ∈ A) (hV0 : V ≠ ∅)
    (hVP : V ⊆ project c A (basicCode c (label c p))) :
    ∃ r : Conditions c, r ≤ p ∧ label c r ∈ V := by
  classical
  have hVc := hAc V hVA
  have hex : ∃ r ∈ V, label c p ⊆ r := by
    by_contra hn
    have hpN : label c p ∈ neg c V := ZFSet.mem_sep.mpr
      ⟨label_mem c p,fun r hr hpr => hn ⟨r,hr,hpr⟩⟩
    have hbN := (basicCode_le_iff c _ _ (label_mem c p) (neg_isCode c V hVc)).mpr hpN
    have hPN := (project_le_iff c A _ _ (regular_isCode c _).1 (hneg V hVA)).mpr hbN
    apply hV0
    apply ZFSet.ext; intro r
    constructor
    · intro hr
      exact False.elim ((ZFSet.mem_sep.mp (hPN (hVP hr))).2 r hr (fun _ h => h))
    · exact fun hr => False.elim (ZFSet.notMem_empty r hr)
  obtain ⟨r,hr,hpr⟩ := hex
  obtain ⟨r,rfl⟩ := label_surjective c (hVc.1 hr)
  exact ⟨r,hpr,hr⟩

theorem quotient_compatible (c A : ZFSet.{0})
    (hAc : ∀ U ∈ A, IsCode c U) (hneg : ∀ U ∈ A, neg c U ∈ A)
    (H : GenericFilter (Conditions (positive A)))
    (p : Conditions c)
    (hp : label c p ∈ InternalQuotientConditions.conditions c A
      (genericFilterSet (positive A) H.carrier))
    (a : Conditions (positive A)) (ha : a ∈ H.carrier) :
    ∃ r : Conditions c, r ≤ p ∧ label c r ∈ label (positive A) a := by
  obtain ⟨b,hb,hbe⟩ := (mem_genericFilterSet _ _ _).mp (ZFSet.mem_sep.mp hp).2
  obtain ⟨v,_,hvb,hva⟩ := H.directed hb ha
  have hvp : label (positive A) v ⊆ project c A (basicCode c (label c p)) := by
    change label (positive A) v ⊆ label (positive A) b at hvb
    rwa [hbe] at hvb
  obtain ⟨r,hr,hrv⟩ := extension_in_code c A hAc hneg p _
    (label_info A v).1 (label_info A v).2 hvp
  exact ⟨r,hr,hva hrv⟩

end TuringRigidity.InternalQuotientLifting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientRequirement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientRequirement
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
attribute [local instance] InternalCollapse.order

theorem requirement_mem (M c a R : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (ha : a ∈ M) (hR : R ∈ M) : requirement c a R ∈ M := by
  let e := cons c (cons a (fun _ => R))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i; exact hc; exact ha; exact hR
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.conj (.subset 0 1) (.existsMem 3
      (.conj (.member 2 0) (.pairMem 1 0 5))))) e he hc
  simpa only [requirement,Formula.Eval,Formula.eval_subset,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using hs

theorem requirement_subset (c a R : ZFSet.{0}) : requirement c a R ⊆ c :=
  fun _ h => (ZFSet.mem_sep.mp h).1

end TuringRigidity.InternalQuotientRequirement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
open InternalBooleanTop InternalQuotientRequirement
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem meets_named_dense (M c B Q A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (τ : Name (Conditions (positive A))) (hτ : τ.encode (label (positive A)) ∈ M)
    (hD : Dense {p : Conditions (InternalQuotientConditions.conditions c A
      (genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier)) |
      label _ p ∈ τ.val (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier}) :
    ∃ p ∈ G.carrier, label c p ∈ τ.val (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
  have hAc : ∀ U ∈ A, IsCode c U := fun U hU => ((hB U).mp (hA.1 hU)).2
  have hpos := positive_mem M A hM hT hAM
  have hH := projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  have hHt : ⊤ ∈ H.carrier := top_in_filter c A (fun U hU => (hAc U hU).1) ht H
  obtain ⟨hoM,ho⟩ := projected_order_code M A hM hT hAM
  let R := CheckedForcingRelation.relation c τ
  have hR : R ∈ M := CheckedForcingRelation.relation_mem M c hM hT hpos hc hoM ho τ hτ
  have htruth (r : Conditions c) : label c r ∈ τ.val H.carrier ↔
      ∃ a ∈ H.carrier, MemForces (Name.check (label c r)) τ a := by
    have hcheck := encoded_check_mem M (positive A) hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpos
      (hM c hc _ (label_mem c r))
    have h := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpos
      hoM ho H hH (Name.check (label c r)) τ hcheck hτ).2
    simpa only [Name.val_check _ hHt] using h
  have hGq : ∀ p ∈ G.carrier, label c p ∈ q :=
    InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G
  let U := requirement c (positive A) R
  have hUM : U ∈ M := requirement_mem M c (positive A) R hM hT hc hpos hR
  rcases generic_decision M c U hM hT hc hUM (requirement_subset c (positive A) R) G hG with hU | hn
  · obtain ⟨p,hp,hpU⟩ := hU
    obtain ⟨_,r,hr,hrp,V,hV,hpV,hrV⟩ := ZFSet.mem_sep.mp hpU
    obtain ⟨r,rfl⟩ := label_surjective c hr
    obtain ⟨a,rfl⟩ := label_surjective (positive A) hV
    have ha : a ∈ H.carrier := ⟨p,hp,hpV⟩
    have hf := (CheckedForcingRelation.pair_relation c (label c r) τ a).mp hrV
    exact ⟨r,G.upper hrp hp,(htruth r).mpr ⟨a,ha,hf.2⟩⟩
  · obtain ⟨p,hp,hpn⟩ := hn
    obtain ⟨pq,hpq⟩ := label_surjective q (hGq p hp)
    obtain ⟨rq,hrq,hrD⟩ := hD pq
    let r := RestrictedForcingFilter.inclusion c q (InternalQuotientConditions.conditions_subset c A _) rq
    have hre : label c r = label q rq := RestrictedForcingFilter.label_inclusion c q _ rq
    have hpr : r ≤ p := by
      change label c p ⊆ label c r
      rw [hre,←hpq]
      exact hrq
    obtain ⟨a,ha,hforce⟩ := (htruth r).mp (hre.symm ▸ hrD)
    have hrqcode : label c r ∈ q := hre.symm ▸ label_mem q rq
    obtain ⟨s,hsr,hsa⟩ := InternalQuotientLifting.quotient_compatible c A hAc hA.2.1 H r hrqcode a ha
    have hsU : label c s ∈ U := ZFSet.mem_sep.mpr ⟨label_mem c s,label c r,label_mem c r,hsr,
      label (positive A) a,label_mem (positive A) a,hsa,
      (CheckedForcingRelation.pair_relation c (label c r) τ a).mpr ⟨label_mem c r,hforce⟩⟩
    exact False.elim ((ZFSet.mem_sep.mp hpn).2 (label c s) hsU (hsr.trans hpr))

theorem quotient_ground_generic (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    GroundGeneric (genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier)
      (quotient M c B Q A hM hT hc hBM hAM hB hQ hA G) := by
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := by
    obtain ⟨p,_⟩ := G.nonempty
    exact fun he => ZFSet.notMem_empty _
      (Eq.mp (congrArg (fun d => label c p ∈ d) he) (label_mem c p))
  let _ := booleanTop c A hcA hc0
  have ht := label_booleanTop c A hcA hc0
  intro D hDN hD
  obtain ⟨τ,hτ,hval⟩ := (mem_extensionSet _ _ _ D).mp hDN
  have hD' := hD
  rw [←hval] at hD'
  obtain ⟨p,hp,hpD⟩ := meets_named_dense M c B Q A hM hT hc hBM hAM hB hQ hA ht G hG τ hτ hD'
  obtain ⟨r,hr,he⟩ := RestrictedForcingFilter.original_condition c _
    (InternalQuotientConditions.conditions_subset c A _) G
    (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G) p hp
  exact ⟨r,hr,he.symm ▸ hval ▸ hpD⟩

end TuringRigidity.InternalQuotientGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientExtension
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalBooleanTop InternalQuotientGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem intermediate_properties (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    let h := genericFilterSet (positive A) H.carrier
    let q := InternalQuotientConditions.conditions c A h
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ h ∈ N ∧ q ∈ N ∧
      InternalCollapse.orderSet q ∈ N := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := by
    obtain ⟨p,_⟩ := G.nonempty
    exact fun he => ZFSet.notMem_empty _
      (Eq.mp (congrArg (fun d => label c p ∈ d) he) (label_mem c p))
  let _ := booleanTop c A hcA hc0
  have ht := label_booleanTop c A hcA hc0
  have hHt := top_in_filter c A (fun U hU => ((hB U).mp (hA.1 hU)).2.1) ht H
  have hpM := positive_mem M A hM hT hAM
  have hHG := projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  obtain ⟨hoM,ho⟩ := projected_order_code M A hM hT hAM
  have hN := genericExtensionSet_transitive M _ hM H.carrier
  have hTN := extension_sourceT M hM hT hpM hoM ho H hHG hHt
  have hMN := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt
  have hhN := genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt
  have hqN := InternalQuotientConditions.conditions_mem _ c A _ hN hTN (hMN hc) (hMN hAM) hhN
    (fun U hU => ((hB U).mp (hA.1 hU)).2)
  exact ⟨hN,hTN,hMN,hhN,hqN,InternalCollapse.orderSet_mem _ hN hTN hqN⟩

theorem extension_eq (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
    genericExtensionSet N q K.carrier = genericExtensionSet M c G.carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  let N := genericExtensionSet M (positive A) H.carrier
  let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
  let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
  obtain ⟨hN,hTN,hMN,_,hqN,hoN⟩ := intermediate_properties M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  have hKG : AtomicForcing.GroundGeneric N K :=
    quotient_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  have hcode : genericFilterSet q K.carrier = genericFilterSet c G.carrier :=
    RestrictedForcingFilter.filterSet_eq c q (InternalQuotientConditions.conditions_subset c A _) G
      (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G)
  let _ : Top (Conditions q) := ⟨Classical.choose K.nonempty⟩
  have hKt : ⊤ ∈ K.carrier := Classical.choose_spec K.nonempty
  have hV := genericExtensionSet_transitive N q hN K.carrier
  have hTV := extension_sourceT N hN hTN hqN hoN (InternalCollapse.orderSet_pair q) K hKG hKt
  have hNV := ground_inclusion_set N q hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity hqN K.carrier hKt
  have hkV := genericFilterSet_mem_extension N q hN hTN.pairing hTN.union hTN.powerSet
    hTN.separation.finitePrefix.bounded hTN.replacement.finitePrefix hTN.infinity hqN K.carrier hKt
  have hgV : genericFilterSet c G.carrier ∈ genericExtensionSet N q K.carrier := hcode ▸ hkV
  have hO := genericExtensionSet_transitive M c hM G.carrier
  have hTO := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair c) G hG hGt
  have hgO := genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hGt
  have hNO := InternalBooleanExtension.projected_extension_subset_original M c B Q A
    hM hT hc hBM hAM hB hQ hA G hG hGt
  have hVO := InternalNameEvaluation.extension_subset N _ hO hTO hNO K.carrier (hcode.symm ▸ hgO)
  have hOV := InternalNameEvaluation.extension_subset M _ hV hTV
    (fun _ hx => hNV (hMN hx)) G.carrier hgV
  exact ZFSet.ext (fun x => ⟨fun hx => hVO hx,fun hx => hOV hx⟩)

end TuringRigidity.InternalQuotientExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealHullQuotient
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealHullQuotient
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalQuotientGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem quotient_over_hull (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier) :
    let X := (InternalNiceName.nice E : Name (Conditions c)).val G.carrier
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let q := InternalQuotientConditions.conditions c A (genericFilterSet (positive A) H.carrier)
    let K := quotient M c B Q A hM hT hc hBM hAM hB hQ hA G
    q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈ RealGeneratedModel.hull M X ∧
      AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) K ∧
      genericExtensionSet (RealGeneratedModel.hull M X) q K.carrier = genericExtensionSet M c G.carrier ∧
      genericFilterSet q K.carrier = genericFilterSet c G.carrier ∧
      ∀ p ∈ G.carrier, ∃ r ∈ K.carrier, label q r = label c p := by
  have he := RealGeneratedModel.projected_extension_eq_hull M c B Q A
    hM hT hc hBM hQM hAM hB hQ hA E hE hgraph hAe G hG hGt
  obtain ⟨_,_,_,_,hq,ho⟩ := InternalQuotientExtension.intermediate_properties M c B Q A
    hM hT hc hBM hAM hB hQ hA G hG
  dsimp only
  rw [←he]
  exact ⟨hq,ho,quotient_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG,
    InternalQuotientExtension.extension_eq M c B Q A hM hT hc hBM hAM hB hQ hA G hG hGt,
    RestrictedForcingFilter.filterSet_eq c _ (InternalQuotientConditions.conditions_subset c A _) G
      (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G),
    RestrictedForcingFilter.original_condition c _ (InternalQuotientConditions.conditions_subset c A _) G
      (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G)⟩

end TuringRigidity.RealHullQuotient

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OriginalRealQuotientModel
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealQuotientModel
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_quotient_oai (M K : ZFSet.{0})
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
                ∃ Gq : GenericFilter (Conditions q), AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) Gq ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericFilterSet q Gq.carrier =
                    genericFilterSet (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier ⊆
                    genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                  ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
                    label q r = label _ (InternalCohenFactor.project _ _ hBA p) := by
  obtain ⟨C,hCM,hCK,hcount,E,hgraph,hE,_,hBA,hread⟩ :=
    InternalCohenColumnReading.internal_column_reading M K hM hT hK τ hτ
  have hω := sourceT_omega_mem M hM hT
  have hKM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK hω
  have hDM := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hCM hω
  have hcM := conditions_mem M _ hM hT hDM
  obtain ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,σ,hσ,hall⟩ :=
    InternalBooleanIntermediate.internal_boolean_intermediate M _ hM hT hcM E hE hgraph
  refine ⟨C,hCM,hCK,hcount,E,hgraph,hE,B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,σ,hσ,hBA,?_⟩
  intro G hG hreal
  obtain ⟨hJG,hJval,_,_⟩ := hread G hG hreal
  let J := InternalCohenProjectedGeneric.projected _ _ hBA G
  obtain ⟨p,hp⟩ := J.nonempty
  have hJtop : ⊤ ∈ J.carrier := J.upper le_top hp
  obtain ⟨H,hHG,hhit,hval,_,_,_,_,_,_⟩ := hall J hJG hJtop
  have hv : σ.val H.carrier = τ.val G.carrier := hval.trans hJval
  have hcar : H.carrier = (projected M _ B Q A hM hT hcM hBM hAM hB hQ hA J).carrier :=
    Set.ext (fun q => hhit q)
  have hHull : genericExtensionSet M (positive A) H.carrier = RealGeneratedModel.hull M (τ.val G.carrier) := by
    rw [hcar,RealGeneratedModel.projected_extension_eq_hull M _ B Q A hM hT hcM hBM hQM hAM hB hQ hA
      E hE hgraph heq J hJG hJtop,hJval]
  have hprop := (RealGeneratedModel.hull_properties M _ B Q A hM hT hcM hBM hQM hAM hB hQ hA
    E hE hgraph heq J hJG hJtop).1
  rw [hJval] at hprop
  refine ⟨H,hHG,hv,hHull,hprop,?_⟩
  dsimp only
  rw [hcar]
  have hfactor := RealHullQuotient.quotient_over_hull M _ B Q A hM hT hcM hBM hQM hAM hB hQ hA
    E hE hgraph heq J hJG hJtop
  dsimp only at hfactor
  rw [hJval] at hfactor
  obtain ⟨hq,ho,hGq,hext,hcode,hcond⟩ := hfactor
  refine ⟨hq,ho,InternalQuotientGeneric.quotient M _ B Q A hM hT hcM hBM hAM hB hQ hA J,
    hGq,hext,hcode,?_,?_⟩
  · rw [hext]
    exact InternalColumnExtension.column_extension_subset M _ _ hM hT hKM hDM hBA G hG
  · intro p hp
    exact hcond _ (InternalCohenProjectedGeneric.projected_contains _ _ hBA G hp)

end TuringRigidity.OriginalRealQuotientModel

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient_oai := @OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient_oai
